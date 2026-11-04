module

public import StacksFrontier.AlgebraicGeometry.Modules.PullbackCompTranspose
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionConormal

/-!
# Base change of the Zariski reading of the conormal module: tools

Let `j : Z ⟶ T`, `j' : Z' ⟶ T'`, `a : Z' ⟶ Z` and `b : T' ⟶ T` be morphisms of test objects with
`j' ≫ b = a ≫ j`.  The naturality of `AlgebraicGeometry.Space.zariskiReadingConormalIso` along
such a square rests on the cocycle law of the base-change map of the Zariski reading
`AlgebraicGeometry.Space.zariskiReadingPullbackHom` under composition of test objects.  This
file collects the ingredients of that cocycle law: the unit of the étale module adjunction of a
composite, the transpose of the base-change map and its value on sections over a Zariski open,
and the compatibility of the identification of sections of a direct image with composition.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_unit_comp_map_eq_unit`: the units of two composable
  adjunctions, read through a comparison of the left adjoints, give the unit of the third.
* `AlgebraicGeometry.Space.etaleModuleAdjunction_unit_comp_modulePullbackCompIso`: the unit of
  the étale module adjunction of a composite, through the composition comparison of Stacks 03LU.
* `AlgebraicGeometry.Space.homEquiv_zariskiReadingPullbackHom_app_val_app`: the transpose of the
  base-change map of the Zariski reading on sections over a Zariski open.
* `AlgebraicGeometry.Space.directImageSelfOpensSection_pushforwardModulesCompAt`: the
  identification of sections of a direct image along a composite of test objects.
* `AlgebraicGeometry.Scheme.Modules.eq_pullbackComp_inv_comp_comp_of_sections`: a morphism out
  of an inverse image along a composite of schemes factors through the composition law as soon
  as its transpose does on sections.
* `AlgebraicGeometry.Space.pointComparison_app_eq_comp_eqToHom` and
  `AlgebraicGeometry.Space.pointComparison_app_congr`: transport of the comparison of
  restricted algebras along equalities of points and of test morphisms.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

/-- The unit of the comparison of left adjoints: the composite of two units, read through an
isomorphism of right adjoints and the comparison `c` of left adjoints, is the third unit. -/
theorem unit_comp_unit_comp_map_eq_unit {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁]
    [Category C₂] {L₁ : C₀ ⥤ C₁} {L₂ : C₁ ⥤ C₂} {L₃ : C₀ ⥤ C₂} {R₁ : C₁ ⥤ C₀} {R₂ : C₂ ⥤ C₁}
    {R₃ : C₂ ⥤ C₀} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (e : R₂ ⋙ R₁ ≅ R₃)
    (c : L₁ ⋙ L₂ ≅ L₃) (hc : c = leftAdjointUniq ((a₁.comp a₂).ofNatIsoRight e) a₃) (M : C₀) :
    (a₁.unit.app M ≫ R₁.map (a₂.unit.app (L₁.obj M)) ≫ e.hom.app _) ≫ R₃.map (c.hom.app M) =
      a₃.unit.app M := by
  subst hc
  rw [← unit_leftAdjointUniq_hom_app ((a₁.comp a₂).ofNatIsoRight e) a₃ M]
  simp [ofNatIsoRight, comp_unit_app]

/-- `CategoryTheory.Adjunction.unit_comp_unit_comp_map_eq_unit`, with the comparison of left
adjoints moved inside the isomorphism of right adjoints. -/
theorem unit_comp_map_unit_comp_map_eq_unit {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁]
    [Category C₂] {L₁ : C₀ ⥤ C₁} {L₂ : C₁ ⥤ C₂} {L₃ : C₀ ⥤ C₂} {R₁ : C₁ ⥤ C₀} {R₂ : C₂ ⥤ C₁}
    {R₃ : C₂ ⥤ C₀} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (e : R₂ ⋙ R₁ ≅ R₃)
    (c : L₁ ⋙ L₂ ≅ L₃) (hc : c = leftAdjointUniq ((a₁.comp a₂).ofNatIsoRight e) a₃) (M : C₀) :
    a₁.unit.app M ≫ R₁.map (a₂.unit.app (L₁.obj M) ≫ R₂.map (c.hom.app M)) ≫
        e.hom.app (L₃.obj M) = a₃.unit.app M := by
  have h := unit_comp_unit_comp_map_eq_unit a₁ a₂ a₃ e c hc M
  have hn := e.hom.naturality (c.hom.app M)
  simp only [Functor.comp_map] at hn
  rw [← h, Functor.map_comp, Category.assoc, Category.assoc, hn, Category.assoc]
  rfl

end CategoryTheory.Adjunction

open AlgebraicGeometry in
/-- `AlgebraicGeometry.Scheme.Modules.eq_pullbackComp_inv_comp_of_sections`, with the second
morphism a composite whose last factor is read on sections directly. -/
theorem AlgebraicGeometry.Scheme.Modules.eq_pullbackComp_inv_comp_comp_of_sections
    {X X' X'' : Scheme.{u}} (q : X'' ⟶ X') (g : X' ⟶ X) {A : X.Modules} {B : X'.Modules}
    {C D : X''.Modules} (c : (Scheme.Modules.pullback g).obj A ⟶ B)
    (c₁ : (Scheme.Modules.pullback q).obj B ⟶ C) (c₂ : C ⟶ D)
    (c'' : (Scheme.Modules.pullback (q ≫ g)).obj A ⟶ D)
    (h : ∀ (O : X.Opens) (x : A.val.obj (op O)),
      ((Scheme.Modules.pullbackPushforwardAdjunction (q ≫ g)).homEquiv A D c'').val.app (op O) x =
        c₂.val.app (op (q ⁻¹ᵁ g ⁻¹ᵁ O))
          (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv B C c₁).val.app
            (op (g ⁻¹ᵁ O))
            (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A B c).val.app (op O) x))) :
    c'' = (Scheme.Modules.pullbackComp q g).inv.app A ≫ (Scheme.Modules.pullback q).map c ≫
      (c₁ ≫ c₂) := by
  refine Scheme.Modules.eq_pullbackComp_inv_comp_of_sections q g c (c₁ ≫ c₂) c'' (fun O x => ?_)
  rw [Adjunction.homEquiv_naturality_right]
  exact h O x

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The unit of the étale module adjunction of a composite is the composite of the units, read
through the composition comparison of Stacks 03LU. -/
theorem etaleModuleAdjunction_unit_comp_modulePullbackCompIso {P' P X : AlgebraicSpaces B S hS}
    (φ : P' ⟶ P) (f : P ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) :
    (etaleModuleAdjunction f).unit.app M ≫
        (smallEtaleRingedToposHom B S hS f).pushforwardModules.map
          ((etaleModuleAdjunction φ).unit.app ((modulePullback B S hS f).obj M) ≫
            (smallEtaleRingedToposHom B S hS φ).pushforwardModules.map
              ((modulePullbackCompIso B S hS φ f).hom.app M)) ≫
        (pushforwardModulesCompAt B S hS φ f).hom.app ((modulePullback B S hS (φ ≫ f)).obj M) =
    (etaleModuleAdjunction (φ ≫ f)).unit.app M :=
  Adjunction.unit_comp_map_unit_comp_map_eq_unit _ _ _ _ _
    (modulePullbackCompIso_eq_leftAdjointUniq_etale φ f) M

/-- `AlgebraicGeometry.Space.etaleModuleAdjunction_unit_comp_modulePullbackCompIso` on sections. -/
theorem etaleModuleAdjunction_unit_comp_modulePullbackCompIso_val_app
    {P' P X : AlgebraicSpaces B S hS} (φ : P' ⟶ P) (f : P ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (U : (SmallEtale B S hS X.1)ᵒᵖ) (v : M.val.obj U) :
    ((pushforwardModulesCompAt B S hS φ f).hom.app ((modulePullback B S hS (φ ≫ f)).obj M)).val.app
        U (((smallEtaleRingedToposHom B S hS f).pushforwardModules.map
          ((etaleModuleAdjunction φ).unit.app ((modulePullback B S hS f).obj M) ≫
            (smallEtaleRingedToposHom B S hS φ).pushforwardModules.map
              ((modulePullbackCompIso B S hS φ f).hom.app M))).val.app U
          (((etaleModuleAdjunction f).unit.app M).val.app U v)) =
      ((etaleModuleAdjunction (φ ≫ f)).unit.app M).val.app U v :=
  congrArg (fun k => k.val.app U v) (etaleModuleAdjunction_unit_comp_modulePullbackCompIso φ f M)

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

/-- The transpose of the base-change map of the Zariski reading. -/
theorem homEquiv_zariskiReadingPullbackHom_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map τ)).homEquiv
        _ _ ((zariskiReadingPullbackHom τ).app N) =
      (zariskiReadingFunctor T).map
          ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
        (zariskiDirectImageNatTrans τ).app _ :=
  Equiv.apply_symm_apply _ _

/-- The transpose of the base-change map of the Zariski reading, on sections over a Zariski
open: the unit of `φ^* ⊣ φ_*` followed by the identification of sections of a direct image. -/
theorem homEquiv_zariskiReadingPullbackHom_app_val_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (x : ((zariskiReadingFunctor T).obj N).val.obj (op O)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map τ)).homEquiv
        _ _ ((zariskiReadingPullbackHom τ).app N)).val.app (op O) x =
      directImageSelfOpensModuleSection τ O
        ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)
        (((zariskiReadingFunctor T).map
          ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N)).val.app
            (op O) x) := by
  have h := congrArg (fun k => k.val.app (op O) x) (homEquiv_zariskiReadingPullbackHom_app τ N)
  refine h.trans ((SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_)
  exact zariskiDirectImageModuleHom_val_app_apply τ _ (op O) _

/-- The identification of sections over a Zariski open of a direct image is natural in the
sheaf of modules. -/
theorem directImageSelfOpensSection_pushforwardModules_map {T T' : BigFppfOver B S hS}
    (τ : T' ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    {M M' : SheafOfModules.{u} (testRing T')} (g : M ⟶ M')
    (v : ((testToposHom τ).pushforwardModules.obj M).val.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection τ O ((Sheaf.moduleSheafFunctor (testRing T')).obj M')
        (((testToposHom τ).pushforwardModules.map g).val.app _ v) =
      g.val.app _ (directImageSelfOpensSection τ O ((Sheaf.moduleSheafFunctor (testRing T')).obj M)
        v) :=
  directImageSelfOpensSection_map τ O ((Sheaf.moduleSheafFunctor (testRing T')).map g) v

/-- The comparison of direct images of a composite of test objects, followed by the
identification of sections over a Zariski open, is the identification along the two factors. -/
theorem directImageSelfOpensSection_pushforwardModulesCompAt {Z' Z T : BigFppfOver B S hS}
    (x : Z' ⟶ Z) (y : Z ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (M : SheafOfModules.{u} (testRing Z'))
    (v : ((testToposHom y).pushforwardModules.obj
      ((testToposHom x).pushforwardModules.obj M)).val.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection (x ≫ y) O ((Sheaf.moduleSheafFunctor (testRing Z')).obj M)
        (((pushforwardModulesCompAt B S hS (representedSpaceMap B S hS x)
          (representedSpaceMap B S hS y)).hom.app M).val.app _ v) =
      directImageSelfOpensSection x (preimageOpens y O)
        ((Sheaf.moduleSheafFunctor (testRing Z')).obj M)
        (directImageSelfOpensSection y O
          ((testToposHom x).toToposHom.pushforward.obj
            ((Sheaf.moduleSheafFunctor (testRing Z')).obj M)) v) :=
  (congrArg (directImageSelfOpensSection (x ≫ y) O ((Sheaf.moduleSheafFunctor (testRing Z')).obj M))
    (pushforwardModulesCompAt_hom_app_val_app _ _ M _ v)).trans
    (directImageSelfOpensSection_comp y x O _ v)


/-- `AlgebraicGeometry.Space.directImageSelfOpensModuleSection` is the identification of sections
of the underlying sheaf. -/
theorem directImageSelfOpensModuleSection_eq {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens) (M : SheafOfModules.{u} (testRing T'))
    (v : ((testToposHom τ).pushforwardModules.obj M).val.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensModuleSection τ O M v =
      directImageSelfOpensSection τ O ((Sheaf.moduleSheafFunctor (testRing T')).obj M) v :=
  rfl

/-- The Zariski reading of a morphism, on sections over a Zariski open. -/
theorem zariskiReadingFunctor_map_val_app {T : BigFppfOver B S hS}
    {M M' : SheafOfModules.{u} (testRing T)} (f : M ⟶ M')
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (v : M.val.obj (op ((selfOpensFunctor B S hS T).obj O))) :
    ((zariskiReadingFunctor T).map f).val.app (op O) v =
      f.val.app (op ((selfOpensFunctor B S hS T).obj O)) v :=
  rfl

/-- Two successive identifications of sections of direct images followed by a morphism, in the
two spellings of the Zariski reading. -/
theorem zariskiReading_map_directImageSelfOpensModuleSection_two {Z' Z T : BigFppfOver B S hS}
    (x : Z' ⟶ Z) (y : Z ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    {L'' : SheafOfModules.{u} (testRing Z)} {L' M : SheafOfModules.{u} (testRing Z')}
    (η : L'' ⟶ (testToposHom x).pushforwardModules.obj L') (m : L' ⟶ M)
    (v : ((testToposHom y).pushforwardModules.obj L'').val.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    ((zariskiReadingFunctor Z').map m).val.app (op (preimageOpens x (preimageOpens y O)))
        (directImageSelfOpensModuleSection x (preimageOpens y O) L'
          (((zariskiReadingFunctor Z).map η).val.app (op (preimageOpens y O))
            (directImageSelfOpensModuleSection y O L'' v))) =
      m.val.app _ (directImageSelfOpensSection x (preimageOpens y O)
        ((Sheaf.moduleSheafFunctor (testRing Z')).obj L')
        (η.val.app _ (directImageSelfOpensSection y O
          ((Sheaf.moduleSheafFunctor (testRing Z)).obj L'') v))) :=
  rfl

/-- The identification of sections of a direct image, after a composite whose last factor is
the direct image of a morphism. -/
theorem directImageSelfOpensSection_comp_pushforwardModules_map {T T' : BigFppfOver B S hS}
    (τ : T' ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    {P : SheafOfModules.{u} (testRing T)} {M M' : SheafOfModules.{u} (testRing T')}
    (g : P ⟶ (testToposHom τ).pushforwardModules.obj M) (m : M ⟶ M')
    (v : P.val.obj (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection τ O ((Sheaf.moduleSheafFunctor (testRing T')).obj M')
        ((g ≫ (testToposHom τ).pushforwardModules.map m).val.app _ v) =
      m.val.app _ (directImageSelfOpensSection τ O ((Sheaf.moduleSheafFunctor (testRing T')).obj M)
        (g.val.app _ v)) :=
  directImageSelfOpensSection_pushforwardModules_map τ O m (g.val.app _ v)

section PointComparison

variable {X : AlgebraicSpaces B S hS}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ)

/-- The comparison of restricted algebras at an arbitrary target point is the one at the
composite point followed by the transport along the equality of points. -/
theorem pointComparison_app_eq_comp_eqToHom {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') :
    (pointComparison A τ f f' hf).app n =
      (pointComparison A τ f (yoneda.map τ ≫ f) rfl).app n ≫
        eqToHom (congrArg (fun g => (zariskiReading T' (etalePointAlgebra A T' g)).piece n)
          hf) := by
  subst hf
  simp

/-- The comparison of restricted algebras along equal morphisms of test objects. -/
theorem pointComparison_app_congr {T T' : BigFppfOver B S hS} {τ₁ τ₂ : T' ⟶ T} (hτ : τ₁ = τ₂)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (h₁ : yoneda.map τ₁ ≫ f = f')
    (h₂ : yoneda.map τ₂ ≫ f = f') :
    (pointComparison A τ₁ f f' h₁).app n =
      (Scheme.Modules.pullbackCongr (congrArg (BigFppfOver.toScheme B S hS).map hτ)).hom.app _ ≫
        (pointComparison A τ₂ f f' h₂).app n := by
  subst hτ
  exact (Category.id_comp _).symm

end PointComparison

end AlgebraicGeometry.Space

end
