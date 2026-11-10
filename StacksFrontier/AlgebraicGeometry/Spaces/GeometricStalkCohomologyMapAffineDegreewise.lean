module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineChase
public import StacksFrontier.Tactic.HEqCongr

/-!
# The chase of Equation 0DKF on affine representables, degree by degree

The degree-`n` components of Stacks 05V5 for complexes and of the degreewise pullback of
associated modules, and the identification of the morphism of complexes produced by the chase of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricStalkCohomologyMapAffineChase.lean` with the
module-level identification `AlgebraicGeometry.Space.representedAffineStalkPathLeft`.

## Main results

* `AlgebraicGeometry.Space.pullbackStalkComplexNatIso_inv_app_f`
* `AlgebraicGeometry.Space.representedAffineComplexPullbackIso_hom_app_f`
* `AlgebraicGeometry.Space.representedAffineStalkPathLeft_hom_app`
* `AlgebraicGeometry.Space.chaseTail_heq_map_representedAffineStalkPathLeft`: the composite of the
  chase is the localization of the degreewise action of the identification through the pullback.
* `AlgebraicGeometry.Space.representedAffineChaseRight_heq`: the ring side of the chase is the
  degreewise action of the identification through the stalk ring maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Generic

/-- Components of the inverse of an isomorphism of the shape of
`AlgebraicGeometry.Space.pullbackStalkComplexNatIso`, given by its defining equation. -/
theorem mapHomologicalComplexCompIso_trans_symm_inv_app_f_of_eq {ι V W W' V' : Type*}
    {c : ComplexShape ι} {_ : Category V} {_ : Category W} {_ : Category W'} {_ : Category V'}
    {_ : Preadditive V} {_ : Preadditive W} {_ : Preadditive W'} {_ : Preadditive V'}
    {F : V ⥤ W} {G : W ⥤ W'} {F' : V ⥤ V'} {G' : V' ⥤ W'}
    {_ : F.Additive} {_ : G.Additive} {_ : F'.Additive} {_ : G'.Additive}
    {_ : (F' ⋙ G').Additive}
    {ρ : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      F'.mapHomologicalComplex c ⋙ G'.mapHomologicalComplex c}
    {e : F ⋙ G ≅ F' ⋙ G'}
    (h : ρ = Functor.mapHomologicalComplexCompIso e c ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).symm)
    (K : HomologicalComplex V c) (i : ι) :
    (ρ.inv.app K).f i = e.inv.app (K.X i) := by
  subst h
  simp

/-- Components of an isomorphism of the shape of
`AlgebraicGeometry.Space.representedAffineComplexPullbackIso`, given by its defining equation. -/
theorem mapHomologicalComplexCompIso_trans_symm_hom_app_f_of_eq {ι V W W' V' : Type*}
    {c : ComplexShape ι} {_ : Category V} {_ : Category W} {_ : Category W'} {_ : Category V'}
    {_ : Preadditive V} {_ : Preadditive W} {_ : Preadditive W'} {_ : Preadditive V'}
    {F : V ⥤ W} {G : W ⥤ W'} {F' : V ⥤ V'} {G' : V' ⥤ W'}
    {_ : F.Additive} {_ : G.Additive} {_ : F'.Additive} {_ : G'.Additive}
    {_ : (F' ⋙ G').Additive}
    {ρ : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      F'.mapHomologicalComplex c ⋙ G'.mapHomologicalComplex c}
    {e : F ⋙ G ≅ F' ⋙ G'}
    (h : ρ = Functor.mapHomologicalComplexCompIso e c ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).symm)
    (K : HomologicalComplex V c) (i : ι) :
    (ρ.hom.app K).f i = e.hom.app (K.X i) := by
  subst h
  simp


/-- The component of a transport between composites differing in their middle factor. -/
theorem eqToIso_hom_app_heq {C C₁ C₂ D : Type*} {_ : Category C} {_ : Category C₁}
    {_ : Category C₂} {_ : Category D} {F G X Y : C ⥤ D} {τ : F ⟶ G} {h : X = Y}
    (hτ : HEq τ (eqToIso h).hom) (hF : F = X) (hG : G = Y) {A : C ⥤ C₁} {E E' : C₁ ⥤ C₂}
    {Q : C₂ ⥤ D} (hX : X = A ⋙ E ⋙ Q) (hY : Y = A ⋙ E' ⋙ Q) (hE : E = E') (K : C) :
    HEq (τ.app K) (Q.map (eqToHom (congrArg (fun F => F.obj (A.obj K)) hE))) := by
  subst hF hG hX hY hE
  obtain rfl := eq_of_heq hτ
  simp

/-- Degree components of the image of a morphism of complexes under a functor. -/
theorem mapHomologicalComplex_map_f_of_eq {ι V W : Type*} {c : ComplexShape ι} {_ : Category V}
    {_ : Category W} {_ : Limits.HasZeroMorphisms V} {_ : Limits.HasZeroMorphisms W} {F : V ⥤ W}
    {_ : F.PreservesZeroMorphisms} {K L : HomologicalComplex V c} {φ : K ⟶ L} {i : ι}
    {g : K.X i ⟶ L.X i} (h : φ.f i = g) : ((F.mapHomologicalComplex c).map φ).f i = F.map g := by
  subst h
  rfl

/-- Four morphisms in a category receiving complexes compose to the image of the morphism of
complexes induced by a natural transformation, as soon as this holds degree by degree. -/
theorem chain_heq_of_degreewise {ι W' D V₀ : Type*} {c c' : ComplexShape ι} {_ : Category W'}
    {_ : Preadditive W'} {_ : Category D} {Q : HomologicalComplex W' c ⥤ D}
    {P₀ P₁ P₁' P₂ P₂' P₃ P₃' P₄ T₀ T₄ : HomologicalComplex W' c}
    {n₁ : P₀ ⟶ P₁} {n₂ : P₁' ⟶ P₂} {n₃ : P₂' ⟶ P₃} {n₄ : P₃' ⟶ P₄} {t : T₀ ⟶ T₄}
    {Y₀ Y₁ Y₂ Y₃ Y₄ : D} {m₁ : Y₀ ⟶ Y₁} {m₂ : Y₁ ⟶ Y₂} {m₃ : Y₂ ⟶ Y₃} {m₄ : Y₃ ⟶ Y₄}
    {A₀ A₁ A₂ A₃ A₄ : ι → W'} {p₁ : ∀ i, A₀ i ⟶ A₁ i} {p₂ : ∀ i, A₁ i ⟶ A₂ i}
    {p₃ : ∀ i, A₂ i ⟶ A₃ i} {p₄ : ∀ i, A₃ i ⟶ A₄ i}
    {_ : Category V₀} {_ : Preadditive V₀} {F G : V₀ ⥤ W'} {_ : F.PreservesZeroMorphisms}
    {_ : G.PreservesZeroMorphisms} {τ : F ⟶ G} {M' : HomologicalComplex V₀ c'}
    (hm₁ : HEq m₁ (Q.map n₁)) (hm₂ : HEq m₂ (Q.map n₂)) (hm₃ : HEq m₃ (Q.map n₃))
    (hm₄ : HEq m₄ (Q.map n₄))
    (htt : HEq t ((NatTrans.mapHomologicalComplex τ c').app M'))
    (hY₀ : Y₀ = Q.obj P₀) (hY₁ : Y₁ = Q.obj P₁) (hY₂ : Y₂ = Q.obj P₂) (hY₃ : Y₃ = Q.obj P₃)
    (hY₄ : Y₄ = Q.obj P₄) (h₁ : P₁ = P₁') (h₂ : P₂ = P₂') (h₃ : P₃ = P₃') (h₀ : P₀ = T₀)
    (h₄ : P₄ = T₄) (hc : c = c') (hT₀ : HEq T₀ ((F.mapHomologicalComplex c').obj M'))
    (hT₄ : HEq T₄ ((G.mapHomologicalComplex c').obj M'))
    (hA₀ : ∀ i, A₀ i = P₀.X i) (hA₁ : ∀ i, A₁ i = P₁.X i) (hA₂ : ∀ i, A₂ i = P₂.X i)
    (hA₃ : ∀ i, A₃ i = P₃.X i) (hA₄ : ∀ i, A₄ i = P₄.X i)
    (hn₁ : ∀ i, HEq (n₁.f i) (p₁ i)) (hn₂ : ∀ i, HEq (n₂.f i) (p₂ i))
    (hn₃ : ∀ i, HEq (n₃.f i) (p₃ i)) (hn₄ : ∀ i, HEq (n₄.f i) (p₄ i))
    (ht : ∀ i, HEq (τ.app (M'.X i)) (p₁ i ≫ p₂ i ≫ p₃ i ≫ p₄ i)) :
    HEq (m₁ ≫ m₂ ≫ m₃ ≫ m₄) (Q.map t) := by
  subst hc
  obtain rfl := eq_of_heq hT₀
  obtain rfl := eq_of_heq hT₄
  obtain rfl := eq_of_heq htt
  subst h₁ h₂ h₃ hY₀ hY₁ hY₂ hY₃ hY₄
  obtain rfl := eq_of_heq hm₁
  obtain rfl := eq_of_heq hm₂
  obtain rfl := eq_of_heq hm₃
  obtain rfl := eq_of_heq hm₄
  obtain rfl : A₀ = fun i => P₀.X i := funext hA₀
  obtain rfl : A₁ = fun i => P₁.X i := funext hA₁
  obtain rfl : A₂ = fun i => P₂.X i := funext hA₂
  obtain rfl : A₃ = fun i => P₃.X i := funext hA₃
  obtain rfl : A₄ = fun i => P₄.X i := funext hA₄
  obtain rfl : p₁ = fun i => n₁.f i := funext fun i => (eq_of_heq (hn₁ i)).symm
  obtain rfl : p₂ = fun i => n₂.f i := funext fun i => (eq_of_heq (hn₂ i)).symm
  obtain rfl : p₃ = fun i => n₃.f i := funext fun i => (eq_of_heq (hn₃ i)).symm
  obtain rfl : p₄ = fun i => n₄.f i := funext fun i => (eq_of_heq (hn₄ i)).symm
  subst h₀
  obtain rfl := h₄
  refine heq_of_eq ?_
  rw [← Q.map_comp, ← Q.map_comp, ← Q.map_comp]
  refine congrArg Q.map (HomologicalComplex.hom_ext _ _ fun i => ?_)
  simp only [HomologicalComplex.comp_f]
  exact (eq_of_heq (ht i)).symm

/-- Degree components of the morphism of complexes induced by a natural transformation. -/
theorem natTrans_mapHomologicalComplex_app_f {ι V W : Type*} {c : ComplexShape ι}
    {_ : Category V} {_ : Category W} {_ : Limits.HasZeroMorphisms V}
    {_ : Limits.HasZeroMorphisms W} {F G : V ⥤ W} {_ : F.PreservesZeroMorphisms}
    {_ : G.PreservesZeroMorphisms} (α : F ⟶ G) (K : HomologicalComplex V c) (i : ι) :
    ((NatTrans.mapHomologicalComplex α c).app K).f i = α.app (K.X i) := rfl

/-- Four composable morphisms of complexes compose to the morphism induced by a natural
transformation, as soon as this holds degree by degree. -/
theorem comp₄_heq_of_degreewise {ι W' V₀ : Type*} {c c' : ComplexShape ι} {_ : Category W'}
    {_ : Preadditive W'} {P₀ P₁ P₂ P₃ P₄ T₀ T₄ : HomologicalComplex W' c}
    {n₁ : P₀ ⟶ P₁} {n₂ : P₁ ⟶ P₂} {n₃ : P₂ ⟶ P₃} {n₄ : P₃ ⟶ P₄} {t : T₀ ⟶ T₄}
    {A₀ A₁ A₂ A₃ A₄ : ι → W'} {p₁ : ∀ i, A₀ i ⟶ A₁ i} {p₂ : ∀ i, A₁ i ⟶ A₂ i}
    {p₃ : ∀ i, A₂ i ⟶ A₃ i} {p₄ : ∀ i, A₃ i ⟶ A₄ i}
    {_ : Category V₀} {_ : Preadditive V₀} {F G : V₀ ⥤ W'} {_ : F.PreservesZeroMorphisms}
    {_ : G.PreservesZeroMorphisms} {τ : F ⟶ G} {M' : HomologicalComplex V₀ c'}
    (htt : HEq t ((NatTrans.mapHomologicalComplex τ c').app M')) (h₀ : P₀ = T₀) (h₄ : P₄ = T₄)
    (hc : c = c') (hT₀ : HEq T₀ ((F.mapHomologicalComplex c').obj M'))
    (hT₄ : HEq T₄ ((G.mapHomologicalComplex c').obj M'))
    (hA₀ : ∀ i, A₀ i = P₀.X i) (hA₁ : ∀ i, A₁ i = P₁.X i) (hA₂ : ∀ i, A₂ i = P₂.X i)
    (hA₃ : ∀ i, A₃ i = P₃.X i) (hA₄ : ∀ i, A₄ i = P₄.X i)
    (hn₁ : ∀ i, HEq (n₁.f i) (p₁ i)) (hn₂ : ∀ i, HEq (n₂.f i) (p₂ i))
    (hn₃ : ∀ i, HEq (n₃.f i) (p₃ i)) (hn₄ : ∀ i, HEq (n₄.f i) (p₄ i))
    (ht : ∀ i, HEq (τ.app (M'.X i)) (p₁ i ≫ p₂ i ≫ p₃ i ≫ p₄ i)) :
    HEq (n₁ ≫ n₂ ≫ n₃ ≫ n₄) t := by
  exact chain_heq_of_degreewise (Q := 𝟭 _) HEq.rfl HEq.rfl HEq.rfl HEq.rfl htt rfl rfl rfl rfl
    rfl rfl rfl rfl h₀ h₄ hc hT₀ hT₄ hA₀ hA₁ hA₂ hA₃ hA₄ hn₁ hn₂ hn₃ hn₄ ht

end Stacks.Generic

namespace AlgebraicGeometry.Space

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X' X : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (x' : GeometricPoint B S hS X'.1)

/-- The degree-`n` component of the inverse of Stacks 05V5 for complexes. -/
theorem pullbackStalkComplexNatIso_inv_app_f (K) (n : ℤ) :
    ((pullbackStalkComplexNatIso g' x').inv.app K).f n =
      (pullbackStalkFunctorIso g' x').inv.app (K.X n) := by
  have := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
    (smallEtaleRingedTopos B S hS X').O
  have := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2) (smallEtaleRingedTopos B S hS X).O
  have := pullbackModules_smallEtale_additive g'
  have := (ModuleCat.extendRestrictScalarsAdj
    (smallEtaleStalkPullbackRingMap B S hS g' x')).left_adjoint_additive
  have : (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
      (smallEtaleRingedTopos B S hS X).O ⋙
    ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g' x')).Additive :=
    inferInstance
  apply Stacks.Generic.mapHomologicalComplexCompIso_trans_symm_inv_app_f_of_eq
    (pullbackStalkComplexNatIso.eq_1 g' x')
  all_goals assumption

end

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

variable {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- The degree-`n` component of the degreewise pullback of associated modules. -/
theorem representedAffineComplexPullbackIso_hom_app_f (K) (n : ℤ) :
    ((representedAffineComplexPullbackIso B S hS g).hom.app K).f n =
      (representedAffineAssociatedPullbackIso B S hS g).hom.app (K.X n) := by
  have := pullbackModules_smallEtale_additive (representedSpaceMap B S hS g)
  have := additive_representedAffineAssociated B S hS U
  have := additive_representedAffineAssociated B S hS U'
  have := (ModuleCat.extendRestrictScalarsAdj
    (representedAffineCommRingCatHom B S hS g).hom).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
      representedAffineAssociated B S hS U').Additive := inferInstance
  apply Stacks.Generic.mapHomologicalComplexCompIso_trans_symm_hom_app_f_of_eq
    (representedAffineComplexPullbackIso.eq_1 B S hS g)
  all_goals assumption

end

section PathLeft

variable {P U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
  (g₀ : P ⟶ U) (x : GeometricPoint B S hS (yoneda.obj P))

/-- The components of the identification through the pullback. -/
theorem representedAffineStalkPathLeft_hom_app
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineStalkPathLeft B S hS g₀ x).hom.app N =
      (eqToHom (congrArg (fun φ => (ModuleCat.extendScalars.{u, u, u} φ).obj
          ((representedAffineStalk B S hS U (geometricPointMap
            (representedSpaceMap B S hS g₀).hom x)).obj N))
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived
          (representedSpaceMap B S hS g₀) x))) ≫
        (pullbackStalkFunctorIso (representedSpaceMap B S hS g₀) x).inv.app
          ((representedAffineAssociated B S hS U).obj N) ≫
        (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj P) x (isAlgebraicSpace_yoneda B S hS P))
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩).O).map
            ((representedAffineAssociatedPullbackIso B S hS g₀).hom.app N) ≫
        (representedAffineStalkIso B S hS P x).inv.app
          ((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).obj N) := by
  simp only [representedAffineStalkPathLeft, representedAffinePullbackStalkIso,
    representedAffinePullbackStalkIso', Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]
  rfl

/-- The pullback-stalk side of the chase of Equation 0DKF, read degree by degree, is induced by the
identification `AlgebraicGeometry.Space.representedAffineStalkPathLeft`. -/
theorem representedAffineChaseLeft_heq
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    HEq ((eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS (⟨yoneda.obj U,
          isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS).obj
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x)
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS).property)
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U,
          isAlgebraicSpace_yoneda B S hS U⟩).O).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived
          (representedSpaceMap B S hS g₀) x))).hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((pullbackStalkComplexNatIso (representedSpaceMap B S hS g₀) x).inv.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj P) x (isAlgebraicSpace_yoneda B S hS P))
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj P,
            isAlgebraicSpace_yoneda B S hS P⟩).O).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ((representedAffineComplexPullbackIso B S hS g₀).hom.app M)) ≫
      DerivedCategory.Q.map ((representedAffineComplexStalkIso B S hS P x).hom.app
        (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)))
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (representedAffineStalkPathLeft B S hS g₀ x).hom
        (ComplexShape.up ℤ)).app M)) := by
  refine Stacks.Generic.chain_heq_of_degreewise
    (by exact (Stacks.Generic.eqToIso_hom_app_heq (by exact HEq.rfl) (by exact rfl) (by exact rfl)
      (by exact rfl) (by exact rfl)
      (by exact (congrArg (fun φ => (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived
          (representedSpaceMap B S hS g₀) x)))
      _))
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl)
    (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl)
    (by exact rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (fun _ => by exact rfl) (fun _ => by exact rfl) (fun _ => by exact rfl) (fun _ => by exact rfl)
    (fun _ => by exact rfl)
    (fun i => by exact heq_of_eq (HomologicalComplex.eqToHom_f _ i))
    (fun i => heq_of_eq (pullbackStalkComplexNatIso_inv_app_f _ _ _ i))
    (fun i => heq_of_eq (Stacks.Generic.mapHomologicalComplex_map_f_of_eq
      (representedAffineComplexPullbackIso_hom_app_f B S hS g₀ M i)))
    (fun i => heq_of_eq (representedAffineComplexStalkIso_hom_app_f B S hS P x _ i)) ?_
  intro i
  refine (heq_of_eq (representedAffineStalkPathLeft_hom_app B S hS g₀ x _)).trans ?_
  heq_congr

/-- **The pullback-stalk side of the chase of Equation 0DKF.** The composite computed by
`AlgebraicGeometry.Space.chaseTail` is the localization of the morphism of complexes induced by
`AlgebraicGeometry.Space.representedAffineStalkPathLeft`. -/
theorem chaseTail_heq_map_representedAffineStalkPathLeft
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    HEq ((extensionGeometricStalkComplexIso (representedSpaceMap B S hS g₀) x).hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        (DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g₀).hom.app M)) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedAssociatedFactors B S hS P).inv.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
      (representedAffineDerivedStalkComparison B S hS P x).hom.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M))
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (representedAffineStalkPathLeft B S hS g₀ x).hom
        (ComplexShape.up ℤ)).app M)) :=
  (heq_of_eq (chaseTail B S hS g₀ x M)).trans
    (HEq.trans (by heq_congr) (representedAffineChaseLeft_heq B S hS g₀ x M))

/-- **The ring side of the chase of Equation 0DKF.** The morphism of complexes computed by
`AlgebraicGeometry.Space.chaseR` is induced degree by degree by the identification
`AlgebraicGeometry.Space.representedAffineStalkPathRight`. -/
theorem representedAffineChaseRight_heq
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    HEq (((ModuleCat.extendScalars.{u, u, u}
          (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ((representedAffineComplexStalkIso B S hS U
              (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).hom.app M) ≫
        (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (representedAffineGlobalStalkRingHom B S hS U (geometricPointMap
            (representedSpaceMap B S hS g₀).hom x))
          (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).inv
            (ComplexShape.up ℤ)).app M ≫
        eqToHom (congrArg (fun φ =>
          ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
          (representedAffineStalkRingHom_square B S hS g₀ x)) ≫
        (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (representedAffineCommRingCatHom B S hS g₀).hom
            (representedAffineGlobalStalkRingHom B S hS P x)).hom
            (ComplexShape.up ℤ)).app M)
      ((NatTrans.mapHomologicalComplex (representedAffineStalkPathRight B S hS g₀ x).hom
        (ComplexShape.up ℤ)).app M) := by
  refine Stacks.Generic.comp₄_heq_of_degreewise HEq.rfl (by exact rfl) (by exact rfl) (by exact rfl)
    (by exact HEq.rfl) (by exact HEq.rfl)
    (fun _ => by exact rfl) (fun _ => by exact rfl) (fun _ => by exact rfl) (fun _ => by exact rfl)
    (fun _ => by exact rfl)
    (fun i => heq_of_eq (Stacks.Generic.mapHomologicalComplex_map_f_of_eq
      (representedAffineComplexStalkIso_hom_app_f B S hS U _ M i)))
    (fun i => heq_of_eq (Stacks.Generic.natTrans_mapHomologicalComplex_app_f _ _ i))
    (fun i => by exact heq_of_eq (HomologicalComplex.eqToHom_f _ i))
    (fun i => heq_of_eq (Stacks.Generic.natTrans_mapHomologicalComplex_app_f _ _ i)) ?_
  intro i
  refine (heq_of_eq (representedAffineStalkPathRight_hom_app B S hS g₀ x _)).trans ?_
  heq_congr

end PathLeft

end AlgebraicGeometry.Space

end
