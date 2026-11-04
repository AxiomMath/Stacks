module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionCompExact
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedLiftedTransitionLeg
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.CategoryTheory.Localization.InducedNatTrans

/-!
# The derived transitions of Stacks 0D9P are induced by the transitions of complexes

Let `S` be a simplicial-site situation with a sheaf of rings `O` on its total site, and let
`φ : [m] ⟶ [n]` be a simplex map whose transition morphism of ringed topoi is flat. The derived
transition `K(φ) : Lf_φ^* K_m ⟶ K_n` of an object `K` of `D(O)` (Stacks 0D9P) is built by lifting
along the localization of the homotopy category. On the image of a complex it is the transition
of complexes `f_φ^*(C_m) ⟶ C_n` of Stacks 09WF, read through the identifications of the derived
restrictions and of `Lf_φ^*` with the functors they induce on complexes.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleTransition_isInducedBy`: the
  derived transition is induced, in the sense of `CategoryTheory.NatTrans.IsInducedBy`, by the
  transition of complexes.

## References

* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section Generic

variable {T : Type u₁} {A : Type u₂} {B : Type u₃}
  [Category.{v₁} T] [Category.{v₂} A] [Category.{v₃} B]
  [Abelian T] [Abelian A] [Abelian B]
  [HasDerivedCategory T] [HasDerivedCategory A] [HasDerivedCategory B]
  (Rn : T ⥤ A) (P : A ⥤ B) (Rm : T ⥤ B)
  [Rn.Additive] [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [Rm.Additive] [PreservesFiniteLimits Rm] [PreservesFiniteColimits Rm]
  (τ : Rn ⋙ P ⟶ Rm)
  (LP : DerivedCategory A ⥤ DerivedCategory B)
  (cmp : DerivedCategory.Qh ⋙ LP ⟶
    P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LP.IsLeftDerivedFunctor cmp (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **A lifted transition is induced by the transition of complexes.** For exact `Rn`, `P`,
`Rm`, a transformation `τ : Rn ⋙ P ⟶ Rm` and a total left derived functor `LP` of `P`, the
transition lifted from `τ` along the localization of the homotopy category is induced, along the
localization of complexes, by the transformation of complexes induced by `τ`. -/
theorem liftedTransition_isInducedBy :
    NatTrans.IsInducedBy (L₁ := DerivedCategory.Q) (L₂ := DerivedCategory.Q)
      (Functor.compFactorization Rn.mapDerivedCategoryFactors
        (Stacks.Homology.leftDerivedFactors P LP cmp))
      Rm.mapDerivedCategoryFactors
      (liftedTransition Rn.mapDerivedCategoryFactorsh cmp Rm.mapDerivedCategoryFactorsh
        (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Rn P Rm τ)
        (HomotopyCategory.quasiIso T (ComplexShape.up ℤ)))
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) := by
  intro C
  let iso := Stacks.Homology.leftDerivedIsoMapDerivedCategory P LP cmp
  rw [liftedTransition_eq_derivedNatTrans Rn P Rm τ cmp iso
    (Stacks.Homology.whiskerLeft_leftDerivedIsoMapDerivedCategory_hom P LP cmp)]
  have h₁ := derivedNatTrans_app_Q (Rn ⋙ P) Rm τ C
  have h₂ := derivedCompIso_refl_inv_app_Q Rn P C
  have h₃ : (Stacks.Homology.leftDerivedFactors P LP cmp).hom.app
      ((Rn.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) =
      iso.hom.app (DerivedCategory.Q.obj ((Rn.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) ≫
        P.mapDerivedCategoryFactors.hom.app
          ((Rn.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
    rfl
  have h₄ := iso.hom.naturality (Rn.mapDerivedCategoryFactors.hom.app C)
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    Category.assoc, h₁, h₂, Functor.compFactorization_hom_app, h₃]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h₄]

end Generic

section Compositor

variable {A : Type*} {B : Type*} {D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (e : F ⋙ G ≅ H)

/-- The comparison `F_D ⋙ G_D ≅ H_D` of derived functors of exact functors induced by an
isomorphism `e : F ⋙ G ≅ H`, as a lift along the localization of complexes. -/
noncomputable def derivedCompLiftIso :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) H.mapDerivedCategory :=
    ⟨H.mapDerivedCategoryFactors⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory)
    (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e _) DerivedCategory.Q)

/-- `derivedCompLiftIso` is induced by the isomorphism of complexes induced by `e`. -/
theorem derivedCompLiftIso_hom_isInducedBy :
    NatTrans.IsInducedBy (L₁ := DerivedCategory.Q) (L₂ := DerivedCategory.Q)
      (Functor.compFactorization F.mapDerivedCategoryFactors G.mapDerivedCategoryFactors)
      H.mapDerivedCategoryFactors (derivedCompLiftIso F G H e).hom
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom := by
  intro C
  simp [derivedCompLiftIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.iso, Functor.compFactorization_hom_app]

end Compositor

section CompositorComp

variable {A : Type*} {BU BV BW : Type*} [Category A] [Category BU] [Category BV] [Category BW]
  [Abelian A] [Abelian BU] [Abelian BV] [Abelian BW]
  [HasDerivedCategory A] [HasDerivedCategory BU] [HasDerivedCategory BV] [HasDerivedCategory BW]
  (FU : A ⥤ BU) (FV : A ⥤ BV) (FW : A ⥤ BW) (Mc : BU ⥤ BV) (Mb : BV ⥤ BW) (Mbc : BU ⥤ BW)
  [FU.Additive] [PreservesFiniteLimits FU] [PreservesFiniteColimits FU]
  [FV.Additive] [PreservesFiniteLimits FV] [PreservesFiniteColimits FV]
  [FW.Additive] [PreservesFiniteLimits FW] [PreservesFiniteColimits FW]
  [Mc.Additive] [PreservesFiniteLimits Mc] [PreservesFiniteColimits Mc]
  [Mb.Additive] [PreservesFiniteLimits Mb] [PreservesFiniteColimits Mb]
  [Mbc.Additive] [PreservesFiniteLimits Mbc] [PreservesFiniteColimits Mbc]
  (ωc : FU ⋙ Mc ≅ FV) (ωb : FV ⋙ Mb ≅ FW) (ωbc : FU ⋙ Mbc ≅ FW) (κ : Mc ⋙ Mb ≅ Mbc)
  (rC : Mbc.mapDerivedCategory ≅ Mc.mapDerivedCategory ⋙ Mb.mapDerivedCategory)

/-- **Compositors of restrictions compose**, on derived categories, when they do on the abelian
categories and the comparison `rC` is induced by `κ`. -/
theorem derivedCompLiftIso_comp
    (hκ : NatTrans.IsInducedBy (L₁ := DerivedCategory.Q) (L₂ := DerivedCategory.Q)
      (Functor.compFactorization Mc.mapDerivedCategoryFactors Mb.mapDerivedCategoryFactors)
      Mbc.mapDerivedCategoryFactors rC.inv
      (Functor.mapHomologicalComplexCompIso κ (ComplexShape.up ℤ)).hom)
    (hu : ∀ M : A, κ.hom.app (FU.obj M) ≫ ωbc.hom.app M = Mb.map (ωc.hom.app M) ≫ ωb.hom.app M)
    (N : DerivedCategory A) :
    rC.inv.app (FU.mapDerivedCategory.obj N) ≫ (derivedCompLiftIso FU Mbc FW ωbc).hom.app N =
      Mb.mapDerivedCategory.map ((derivedCompLiftIso FU Mc FV ωc).hom.app N) ≫
        (derivedCompLiftIso FV Mb FW ωb).hom.app N := by
  have hL := (NatTrans.IsInducedBy.whiskerLeft FU.mapDerivedCategoryFactors hκ).comp
    (derivedCompLiftIso_hom_isInducedBy FU Mbc FW ωbc)
  have hR := (NatTrans.IsInducedBy.associator_inv FU.mapDerivedCategoryFactors
      Mc.mapDerivedCategoryFactors Mb.mapDerivedCategoryFactors).comp
    ((NatTrans.IsInducedBy.whiskerRight (derivedCompLiftIso_hom_isInducedBy FU Mc FV ωc)
      Mb.mapDerivedCategoryFactors).comp (derivedCompLiftIso_hom_isInducedBy FV Mb FW ωb))
  have e := hL.ext_of_eq (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) hR (by
    refine NatTrans.ext (funext fun C ↦ HomologicalComplex.hom_ext _ _ fun p ↦ ?_)
    simpa using hu (C.X p))
  simpa using NatTrans.congr_app e N

end CompositorComp

section Compatibility

variable {MC MT Mm Mn MUn MUm : Type*} [Category MC] [Category MT] [Category Mm] [Category Mn]
  [Category MUn] [Category MUm] [Abelian MC] [Abelian MT] [Abelian Mm] [Abelian Mn]
  [Abelian MUn] [Abelian MUm] [HasDerivedCategory MC] [HasDerivedCategory MT]
  [HasDerivedCategory Mm] [HasDerivedCategory Mn] [HasDerivedCategory MUn]
  [HasDerivedCategory MUm]
  (R : MC ⥤ MT) (Cm : MT ⥤ Mm) (Cn : MT ⥤ Mn) (P : Mm ⥤ Mn) (Sn : Mn ⥤ MUn) (Sm : Mm ⥤ MUm)
  (M : MUm ⥤ MUn) (OU : MC ⥤ MUn) (OU' : MC ⥤ MUm)
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [Cm.Additive] [PreservesFiniteLimits Cm] [PreservesFiniteColimits Cm]
  [Cn.Additive] [PreservesFiniteLimits Cn] [PreservesFiniteColimits Cn]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [Sn.Additive] [PreservesFiniteLimits Sn] [PreservesFiniteColimits Sn]
  [Sm.Additive] [PreservesFiniteLimits Sm] [PreservesFiniteColimits Sm]
  [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [OU.Additive] [PreservesFiniteLimits OU] [PreservesFiniteColimits OU]
  [OU'.Additive] [PreservesFiniteLimits OU'] [PreservesFiniteColimits OU']
  (τ : Cm ⋙ P ⟶ Cn) (θn : R ⋙ Cn ⋙ Sn ≅ OU) (θm : R ⋙ Cm ⋙ Sm ≅ OU')
  (π : P ⋙ Sn ≅ Sm ⋙ M) (ω : OU' ⋙ M ≅ OU)
  (LP : DerivedCategory Mm ⥤ DerivedCategory Mn)
  (cmp : DerivedCategory.Qh ⋙ LP ⟶
    P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LP.IsLeftDerivedFunctor cmp (HomotopyCategory.quasiIso Mm (ComplexShape.up ℤ))]

/-- The identification `(R E)_{n,i} ≅ O_U E` of derived functors induced by `θn`. -/
noncomputable abbrev derivedRestrictionIso :
    R.mapDerivedCategory ⋙ Cn.mapDerivedCategory ⋙ Sn.mapDerivedCategory ≅ OU.mapDerivedCategory :=
  NatIso.liftAlong (HomologicalComplex.quasiIso MC (ComplexShape.up ℤ))
    (Functor.compFactorization R.mapDerivedCategoryFactors
      (Functor.compFactorization Cn.mapDerivedCategoryFactors Sn.mapDerivedCategoryFactors))
    OU.mapDerivedCategoryFactors (NatIso.mapHomologicalComplex θn (ComplexShape.up ℤ))

/-- **Derived transitions under restriction identifications, from the underived ones.** If, on
sheaves, the transition `τ` followed by `θn` is `π` followed by `θm` and `ω`, then the same holds
for the derived transition lifted from `τ`, the derived identifications lifted from `θn`, `θm`,
`π`, and the derived comparison of `ω`. -/
theorem derived_transition_restriction_compat
    (hu : ∀ X : MC, Sn.map (τ.app (R.obj X)) ≫ θn.hom.app X =
      π.hom.app (Cm.obj (R.obj X)) ≫ M.map (θm.hom.app X) ≫ ω.hom.app X)
    (N : DerivedCategory MC) :
    Sn.mapDerivedCategory.map ((liftedTransition Cm.mapDerivedCategoryFactorsh cmp
          Cn.mapDerivedCategoryFactorsh
          (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Cm P Cn τ)
          (HomotopyCategory.quasiIso MT (ComplexShape.up ℤ))).app
            (R.mapDerivedCategory.obj N)) ≫
        (derivedRestrictionIso R Cn Sn OU θn).hom.app N =
      (NatIso.liftAlong (HomologicalComplex.quasiIso Mm (ComplexShape.up ℤ))
          (Functor.compFactorization (Stacks.Homology.leftDerivedFactors P LP cmp)
            Sn.mapDerivedCategoryFactors)
          (Functor.compFactorization Sm.mapDerivedCategoryFactors M.mapDerivedCategoryFactors)
          (NatIso.mapHomologicalComplex π (ComplexShape.up ℤ))).hom.app
            (Cm.mapDerivedCategory.obj (R.mapDerivedCategory.obj N)) ≫
        M.mapDerivedCategory.map ((derivedRestrictionIso R Cm Sm OU' θm).hom.app N) ≫
          (derivedCompLiftIso OU' M OU ω).hom.app N := by
  have hL := (NatTrans.IsInducedBy.whiskerLeft R.mapDerivedCategoryFactors
    (NatTrans.IsInducedBy.whiskerRight (liftedTransition_isInducedBy Cm P Cn τ LP cmp)
      Sn.mapDerivedCategoryFactors)).comp
    (NatTrans.isInducedBy_liftAlong (HomologicalComplex.quasiIso MC (ComplexShape.up ℤ))
      (Functor.compFactorization R.mapDerivedCategoryFactors
        (Functor.compFactorization Cn.mapDerivedCategoryFactors Sn.mapDerivedCategoryFactors))
      OU.mapDerivedCategoryFactors (NatIso.mapHomologicalComplex θn (ComplexShape.up ℤ)).hom)
  have hR := (NatTrans.IsInducedBy.whiskerLeft R.mapDerivedCategoryFactors
    (NatTrans.IsInducedBy.associator Cm.mapDerivedCategoryFactors
      (Stacks.Homology.leftDerivedFactors P LP cmp) Sn.mapDerivedCategoryFactors)).comp
    ((NatTrans.IsInducedBy.whiskerLeft R.mapDerivedCategoryFactors
      (NatTrans.IsInducedBy.whiskerLeft Cm.mapDerivedCategoryFactors
        (NatTrans.isInducedBy_liftAlong (HomologicalComplex.quasiIso Mm (ComplexShape.up ℤ))
          (Functor.compFactorization (Stacks.Homology.leftDerivedFactors P LP cmp)
            Sn.mapDerivedCategoryFactors)
          (Functor.compFactorization Sm.mapDerivedCategoryFactors M.mapDerivedCategoryFactors)
          (NatIso.mapHomologicalComplex π (ComplexShape.up ℤ)).hom))).comp
    ((NatTrans.IsInducedBy.whiskerLeft R.mapDerivedCategoryFactors
      (NatTrans.IsInducedBy.associator_inv Cm.mapDerivedCategoryFactors
        Sm.mapDerivedCategoryFactors M.mapDerivedCategoryFactors)).comp
    ((NatTrans.IsInducedBy.associator_inv R.mapDerivedCategoryFactors
      (Functor.compFactorization Cm.mapDerivedCategoryFactors Sm.mapDerivedCategoryFactors)
      M.mapDerivedCategoryFactors).comp
    ((NatTrans.IsInducedBy.whiskerRight
      (NatTrans.isInducedBy_liftAlong (HomologicalComplex.quasiIso MC (ComplexShape.up ℤ))
        (Functor.compFactorization R.mapDerivedCategoryFactors
          (Functor.compFactorization Cm.mapDerivedCategoryFactors Sm.mapDerivedCategoryFactors))
        OU'.mapDerivedCategoryFactors (NatIso.mapHomologicalComplex θm (ComplexShape.up ℤ)).hom)
      M.mapDerivedCategoryFactors).comp
    (derivedCompLiftIso_hom_isInducedBy OU' M OU ω)))))
  have e := hL.ext_of_eq (HomologicalComplex.quasiIso MC (ComplexShape.up ℤ)) hR (by
    refine NatTrans.ext (funext fun C ↦ HomologicalComplex.hom_ext _ _ fun p ↦ ?_)
    simpa using hu (C.X p))
  simpa using NatTrans.congr_app e N

end Compatibility

end CategoryTheory

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The derived transition `K(φ)` of Stacks 0D9P is induced by the transition of complexes**,
for a flat transition morphism: on the image `Q(C)` of a complex, `K(φ)` composed with the
identification of `(Q C)_n` is the identification of `Lf_φ^*(Q C)_m` composed with the transition
`f_φ^*(C_m) ⟶ C_n` of complexes. -/
theorem derivedComponentModuleTransition_isInducedBy {m n : SimplexCategory} (φ : m ⟶ n)
    (hφ : (S.transitionRingedToposHom O φ).IsFlat) :
    letI := S.transitionPullbackModules_preservesFiniteLimits O φ hφ
    NatTrans.IsInducedBy (L₁ := DerivedCategory.Q) (L₂ := DerivedCategory.Q)
      (Functor.compFactorization (S.componentModulesRestriction O m).mapDerivedCategoryFactors
        (S.derivedTransitionPullbackFactors O φ hφ))
      (S.componentModulesRestriction O n).mapDerivedCategoryFactors
      (S.derivedComponentModuleTransition O φ)
      (NatTrans.mapHomologicalComplex (S.componentModulesTransition O φ) (ComplexShape.up ℤ)) :=
  let := S.transitionPullbackModules_preservesFiniteLimits O φ hφ
  liftedTransition_isInducedBy (S.componentModulesRestriction O m)
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.componentModulesRestriction O n) (S.componentModulesTransition O φ)
    (S.derivedTransitionPullback O φ) (S.derivedTransitionComparison O φ)

end CategoryTheory.SimplicialSiteSituation

end
