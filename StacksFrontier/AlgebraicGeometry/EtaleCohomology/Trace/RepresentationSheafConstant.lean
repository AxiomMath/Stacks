module

public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.ConstantSheafModuleDictionary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf `ℱ_ρ` of a trivial action is constant

Let `X` be a connected scheme with a geometric point `x` and `Λ` a finite ring. For a finite
`Λ`-module `M` on which `π₁(X, x)` acts trivially, the sheaf `ℱ_M` attached to it by Tag 0DV5 (3)
is the constant sheaf with value `M`, naturally in `M`.

## Main definitions

* `Stacks.GroupCohomology.finiteTypeContinuousModuleTrivial` — a finite `Λ`-module with the
  trivial action of `G`, as a functor of the module.
* `AlgebraicGeometry.representationSheafTrivialIsoConstant` — `ℱ_M ≅ M_X`, naturally in `M`.

## Implementation notes

The comparison map `M_X ⟶ ℱ_M` is the adjoint transpose, along the constant sheaf / global
sections adjunction, of the identification `M = M^{π₁} ≅ Γ(X, ℱ_M)` of
`AlgebraicGeometry.representationSheafGlobalSectionsIso`. That it is an isomorphism is local, and
it is checked after restriction along a covering trivializing `ℱ_M`.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.GroupCohomology

universe u r u' w

namespace Stacks.GroupCohomology

open Stacks.DiscreteModuleTopology

variable (Λ : Type r) [Ring Λ] (G : Type u') [Group G] [TopologicalSpace G]

/-- **A finite `Λ`-module with the trivial action of `G`**, as a functor from finite modules. -/
@[sga "5 IIIB 6.18" "more general"]
def finiteTypeContinuousModuleTrivial :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{w} Λ) ⥤
      FiniteTypeContinuousModule.{r, u', w} Λ G where
  obj M := ⟨⟨⟨Action.trivial G M.obj, (Action.isContinuous_def _).2 continuous_snd⟩, ⟨rfl⟩⟩,
    M.property⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := f.hom
      comm := fun _ ↦ rfl }))

/-- The invariants of a trivial action are the whole module. -/
def finiteTypeContinuousModuleTrivialInvariantsIso :
    finiteTypeContinuousModuleTrivial Λ G ⋙ finiteTypeContinuousModuleInvariants Λ G ≅
      ObjectProperty.ι _ :=
  NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    { toFun := fun x ↦ x.1
      invFun := fun x ↦ ⟨x, fun _ ↦ rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl })
    (fun _ ↦ by ext; rfl)

/-- The action underlying a finite `Λ`-module with continuous `G`-action. -/
abbrev finiteTypeContinuousModuleToAction :
    FiniteTypeContinuousModule.{r, u', w} Λ G ⥤ Action (ModuleCat.{w} Λ) G :=
  finiteTypeContinuousModuleι Λ G ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _

/-- **A morphism of finite `Λ`-modules with continuous `G`-action whose underlying map is
bijective is an isomorphism.** -/
theorem isIso_of_bijective {P Q : FiniteTypeContinuousModule.{r, u', w} Λ G} (f : P ⟶ Q)
    (hf : Function.Bijective ((finiteTypeContinuousModuleToAction Λ G).map f).hom) : IsIso f := by
  have : IsIso f.hom.hom.hom.hom := (ConcreteCategory.isIso_iff_bijective _).2 hf
  have h₁ : IsIso f.hom.hom.hom := Action.isIso_of_hom_isIso _
  have h₂ : IsIso f.hom.hom :=
    have : IsIso ((ObjectProperty.ι _).map f.hom.hom) := h₁
    (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map f.hom.hom
  have h₃ : IsIso f.hom :=
    have : IsIso ((ObjectProperty.ι _).map f.hom) := h₂
    (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map f.hom
  have : IsIso ((ObjectProperty.ι _).map f) := h₃
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map f

/-- Every element of a module with trivial action is invariant. -/
theorem mem_finiteTypeContinuousModuleInvariantsSubmodule_of_rho_eq_one
    {P : FiniteTypeContinuousModule.{r, u', w} Λ G} (hP : ∀ g, P.obj.obj.obj.ρ g = 1)
    (v : P.obj.obj.obj.V) : v ∈ finiteTypeContinuousModuleInvariantsSubmodule Λ G P :=
  fun g ↦ by rw [hP g]; rfl

/-- A module isomorphic to one with the trivial action has the trivial action. -/
theorem rho_apply_eq_of_iso {P Q : FiniteTypeContinuousModule.{r, u', w} Λ G} (c : P ≅ Q)
    (hQ : ∀ g (v : Q.obj.obj.obj.V), ConcreteCategory.hom (Q.obj.obj.obj.ρ g).asHom v = v) (g : G)
    (v : P.obj.obj.obj.V) : ConcreteCategory.hom (P.obj.obj.obj.ρ g).asHom v = v := by
  let F := finiteTypeContinuousModuleToAction Λ G
  have hinj : Function.Injective (F.map c.hom).hom :=
    (ConcreteCategory.bijective_of_isIso ((Action.forget (ModuleCat.{w} Λ) G).mapIso
      (F.mapIso c)).hom).1
  exact hinj ((ConcreteCategory.congr_hom ((F.map c.hom).comm g) v).trans (hQ g _))

end Stacks.GroupCohomology

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type r) [Ring Λ] [Finite Λ]

omit [ConnectedSpace X.1] [Finite Λ] in
/-- Sheafification of presheaves of `Λ`-modules on the small étale site of Stacks 021B, at the
module universe of Tag 0DV5. -/
local instance hasSheafify_smallEtale_moduleCat :
    HasSheafify (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{u + 1} Λ _

/-- The sheaf of the trivial action, on the site of Stacks 021B. -/
abbrev trivialRepresentationSheafSmall :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ) ⥤
      Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) :=
  finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x) ⋙
    (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙ ObjectProperty.ι _

/-- **Global sections of the sheaf of a trivial action are the module**, naturally. -/
def trivialRepresentationSheafSmallSectionsIso :
    trivialRepresentationSheafSmall B X x Λ ⋙
        (sheafSections (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)).obj
          (op (SmallEtale.final B X.1 X.2)) ≅
      ObjectProperty.ι _ :=
  Functor.isoWhiskerLeft (finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x))
      (Functor.isoWhiskerLeft (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse
          (finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants B X x Λ).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso
          _ ≪≫ Functor.leftUnitor _) ≪≫
    finiteTypeContinuousModuleTrivialInvariantsIso Λ (EtaleFundamentalGroup X.1 x)

/-- The comparison `M_X ⟶ ℱ_M` from the constant sheaf to the sheaf of the trivial action: the
adjoint transpose of `M ≅ Γ(X, ℱ_M)`. -/
def constantToTrivialRepresentationSheafSmall :
    ObjectProperty.ι _ ⋙ constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ⟶
      trivialRepresentationSheafSmall B X x Λ where
  app M := ((constantSheafAdj (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)
    (SmallEtale.finalIsTerminal B X.1 X.2)).homEquiv _ _).symm
      ((trivialRepresentationSheafSmallSectionsIso B X x Λ).inv.app M)
  naturality M N g := by
    apply ((constantSheafAdj (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)
      (SmallEtale.finalIsTerminal B X.1 X.2)).homEquiv _ _).injective
    rw [Functor.comp_map, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (trivialRepresentationSheafSmallSectionsIso B X x Λ).inv.naturality g

omit [Finite Λ] in
/-- A morphism of modules through which an isomorphism factors is surjective. -/
theorem surjective_of_comp_eq_iso_hom {A C D : ModuleCat.{w} Λ} (u : A ⟶ C) (g : C ⟶ D)
    (e : A ≅ D) (h : u ≫ g = e.hom) : Function.Surjective g := fun d ↦
  ⟨u (e.inv d), by rw [← ConcreteCategory.comp_apply, h, Iso.inv_hom_id_apply]⟩

omit [Finite Λ] in
/-- In a commutative square of modules whose two vertical sides are isomorphisms, the top side
is bijective if the bottom side is. -/
theorem bijective_of_comm_sq_of_iso {A B C D : ModuleCat.{w} Λ} {f : A ⟶ B} {g : C ⟶ D}
    (e₁ : A ≅ C) (e₂ : B ≅ D) (h : f ≫ e₂.hom = e₁.hom ≫ g) (hg : Function.Bijective g) :
    Function.Bijective f := by
  refine (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso e₂.hom) f).1 ?_
  have : (fun v ↦ e₂.hom (f v)) = fun v ↦ g (e₁.hom v) := funext (ConcreteCategory.congr_hom h)
  rw [Function.comp_def, this]
  exact hg.comp (ConcreteCategory.bijective_of_isIso e₁.hom)

/-- The comparison `M_X ⟶ ℱ_M` induces a surjection on global sections: composed with the unit
of the constant sheaf / global sections adjunction it is the isomorphism `M ≅ Γ(X, ℱ_M)`. -/
theorem surjective_sections_constantToTrivialRepresentationSheafSmall
    (M : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    Function.Surjective (((constantToTrivialRepresentationSheafSmall B X x Λ).app M).hom.app
      (op (SmallEtale.final B X.1 X.2))) := by
  have h := ((constantSheafAdj (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)
    (SmallEtale.finalIsTerminal B X.1 X.2)).homEquiv_unit (X := M.obj)
      (Y := (trivialRepresentationSheafSmall B X x Λ).obj M)
      ((constantToTrivialRepresentationSheafSmall B X x Λ).app M))
  have h2 : ((constantSheafAdj (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)
      (SmallEtale.finalIsTerminal B X.1 X.2)).homEquiv _ _)
        ((constantToTrivialRepresentationSheafSmall B X x Λ).app M) =
      (trivialRepresentationSheafSmallSectionsIso B X x Λ).inv.app M :=
    Equiv.apply_symm_apply _ _
  exact surjective_of_comp_eq_iso_hom Λ _ _
    ((trivialRepresentationSheafSmallSectionsIso B X x Λ).app M).symm (h2.symm.trans h).symm

/-- The comparison `M_X ⟶ ℱ_M` is bijective on global sections: it is surjective there, and both
sides have as many global sections as `M` has elements. -/
theorem bijective_sections_constantToTrivialRepresentationSheafSmall
    (M : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) [Finite (ToType M.obj)] :
    Function.Bijective ((finiteTypeLocallyConstantModuleSheafSections B X Λ).map
      (ObjectProperty.homMk ((constantToTrivialRepresentationSheafSmall B X x Λ).app M) :
        constantSheafFiniteTypeLocallyConstantModule B X Λ M.obj ⟶
          (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj
            ((finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x)).obj M))) := by
  have eC : ToType ((finiteTypeLocallyConstantModuleSheafSections B X Λ).obj
      (constantSheafFiniteTypeLocallyConstantModule B X Λ M.obj)) ≃ ToType M.obj :=
    ((finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants B X x Λ).app
        (constantSheafFiniteTypeLocallyConstantModule B X Λ M.obj)).symm.toLinearEquiv.toEquiv.trans
      ((Equiv.subtypeUnivEquiv (mem_finiteTypeContinuousModuleInvariantsSubmodule_of_rho_eq_one Λ _
        (rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf B X Λ x
          M.obj))).trans
        (finiteTypeLocallyConstantModuleSheafEquivalenceConstantSheafEquiv B X Λ x M.obj))
  have eG : ToType ((finiteTypeLocallyConstantModuleSheafSections B X Λ).obj
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj
        ((finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x)).obj M))) ≃
        ToType M.obj :=
    ((trivialRepresentationSheafSmallSectionsIso B X x Λ).app M).toLinearEquiv.toEquiv
  have : Finite (ToType ((finiteTypeLocallyConstantModuleSheafSections B X Λ).obj
      (constantSheafFiniteTypeLocallyConstantModule B X Λ M.obj))) :=
    Finite.of_equiv _ eC.symm
  exact Function.Surjective.bijective_of_nat_card_le
    (surjective_sections_constantToTrivialRepresentationSheafSmall B X x Λ M)
    ((Nat.card_congr eC).trans (Nat.card_congr eG).symm).le

/-- **The comparison `M_X ⟶ ℱ_M` is an isomorphism**, on the site of Stacks 021B. On global
sections it is surjective, and both sides have as many global sections as `M` has elements, so it
is bijective there; through the identification of global sections with invariants, and since
both `π₁`-modules carry the trivial action, it is bijective on the `π₁`-modules, hence an
isomorphism. -/
theorem isIso_constantToTrivialRepresentationSheafSmall
    (M : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    IsIso ((constantToTrivialRepresentationSheafSmall B X x Λ).app M) := by
  have : Finite (ToType M.obj) := (moduleCat_isFG_iff_finite Λ M.obj).1 M.property
  let φ' : constantSheafFiniteTypeLocallyConstantModule B X Λ M.obj ⟶
      (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj
        ((finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x)).obj M) :=
    ObjectProperty.homMk ((constantToTrivialRepresentationSheafSmall B X x Λ).app M)
  have hinv : Function.Bijective ((finiteTypeContinuousModuleInvariants Λ
      (EtaleFundamentalGroup X.1 x)).map
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.map φ')) :=
    bijective_of_comm_sq_of_iso Λ
      ((finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants B X x Λ).app _)
      ((finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants B X x Λ).app _)
      ((finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants B X x Λ).hom.naturality φ')
      (bijective_sections_constantToTrivialRepresentationSheafSmall B X x Λ M)
  have hQ := rho_apply_eq_of_iso Λ (EtaleFundamentalGroup X.1 x)
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app
      ((finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x)).obj M))
    (fun _ _ ↦ rfl)
  let eP := Equiv.subtypeUnivEquiv (mem_finiteTypeContinuousModuleInvariantsSubmodule_of_rho_eq_one
    Λ _ (rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf B X Λ x M.obj))
  let eQ := Equiv.subtypeUnivEquiv (p := (· ∈ finiteTypeContinuousModuleInvariantsSubmodule Λ
      (EtaleFundamentalGroup X.1 x)
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj
          ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj
            ((finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x)).obj M)))))
    (fun v g ↦ hQ g v)
  have hund : Function.Bijective ((finiteTypeContinuousModuleToAction Λ
      (EtaleFundamentalGroup X.1 x)).map
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.map φ')).hom :=
    eQ.bijective.comp (hinv.comp eP.symm.bijective)
  have := isIso_of_bijective Λ _ _ hund
  have : IsIso φ' :=
    isIso_of_reflects_iso φ' (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor
  exact inferInstanceAs (IsIso ((ObjectProperty.ι _).map φ'))

/-- **The constant sheaf is the sheaf of the trivial action**, on the site of Stacks 021B,
naturally in the finite module. -/
def constantIsoTrivialRepresentationSheafSmall :
    ObjectProperty.ι _ ⋙ constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ≅
      trivialRepresentationSheafSmall B X x Λ :=
  NatIso.ofComponents
    (fun M ↦ haveI := isIso_constantToTrivialRepresentationSheafSmall B X x Λ M
      asIso ((constantToTrivialRepresentationSheafSmall B X x Λ).app M))
    (fun g ↦ (constantToTrivialRepresentationSheafSmall B X x Λ).naturality g)

omit [ConnectedSpace X.1] [Finite Λ] in
/-- Sheafification of presheaves of `Λ`-modules with lifted coefficients on the small étale site
of Stacks 021B. -/
local instance hasSheafify_smallEtale_moduleCat_max :
    HasSheafify (SmallEtale.topology B X.1 X.2) (ModuleCat.{max (u + 1) r} Λ) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{max (u + 1) r} Λ _

/-- **`ℱ_M` is the constant sheaf `M_X` for a trivial action**, on Mathlib's small étale site and
with the coefficients of `AlgebraicGeometry.representationSheaf`: for a finite `Λ`-module `M` with
the trivial action of `π₁(X, x)`, the sheaf attached to it is the constant sheaf with value `M`
(lifted to the coefficient universe), naturally in `M`. -/
def representationSheafTrivialIsoConstant :
    finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 x) ⋙
        representationSheaf B X x Λ ≅
      ObjectProperty.ι _ ⋙ ModuleCat.uliftFunctor.{r, u + 1} Λ ⋙
        constantSheaf X.1.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) := by
  letI := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ
  haveI : ∀ Z : (X.1.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Z (SmallEtale.toEtaleSite B X.1 X.2).op) (ModuleCat.{max (u + 1) r} Λ) :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  exact Functor.isoWhiskerRight (constantIsoTrivialRepresentationSheafSmall B X x Λ).symm
      (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{r, u + 1} Λ) ⋙
        (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{max (u + 1) r} Λ)).functor) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (constantCommuteCompose (SmallEtale.topology B X.1 X.2)
          (ModuleCat.uliftFunctor.{r, u + 1} Λ)) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{r, u + 1} Λ)
          (Functor.isoWhiskerRight (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
              (SmallEtale.topology B X.1 X.2) X.1.smallEtaleTopology
              (SmallEtale.toEtaleSite B X.1 X.2) (ModuleCat.{max (u + 1) r} Λ)).symm _ ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _
              (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{max (u + 1) r} Λ)).counitIso ≪≫
            Functor.rightUnitor _))

end AlgebraicGeometry
