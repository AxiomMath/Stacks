module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteTypeContinuousModuleCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.InverseImageRepresentedSections

/-!
# The tautological section of `ℱ_ρ` over its representing cover

Let `X` be a connected scheme with a geometric point `x`, `Λ` a finite ring and `ρ` a finite
`Λ`-module `M` with a continuous action of `π₁(X, x)`, with sheaf `ℱ_ρ`
(`AlgebraicGeometry.representationSheaf`, built from Tag 0DV5). The sheaf of sets underlying `ℱ_ρ`
is finite locally constant, hence represented by a finite étale cover `V` of `X` (Tag 03RV). This
file records the representing data explicitly:

* the cover `V` (`AlgebraicGeometry.representationCover` on Mathlib's small étale site,
  `AlgebraicGeometry.representationFiniteEtaleCover` as a finite étale cover), as a functor of `ρ`;
* the tautological section `ε ∈ ℱ_ρ(V)` (`AlgebraicGeometry.representationTautologicalSection`),
  which represents the underlying sheaf of sets of `ℱ_ρ`
  (`AlgebraicGeometry.isIso_sectionEquiv_symm_representationTautologicalSection`);
* the identification of the geometric fibre of `V` at `x` with `M`
  (`AlgebraicGeometry.representationFibreEquiv`), which intertwines the monodromy with `ρ`, carries
  morphisms of covers induced by morphisms of representations to those morphisms, and carries the
  cover endomorphisms representing scalars to the scalars;
* the naturality of `ε` in `ρ` and its behaviour under scalars.

## Implementation notes

Nothing here is chosen beyond the inverses of the equivalences of Tags 0DV5 and 03RV and of the
comparison of the two presentations of the small étale site, and every statement is transported
through their units and counits. The fibre of the representing cover is identified with `M`
element for element by `AlgebraicGeometry.geometricFibreSetEquiv`: the underlying set, the action
of `π₁(X, x)` and the action of `Λ` on the module of Tag 0DV5 (3) are, definitionally, those of the
finite `π₁(X, x)`-set of Tag 0DV5 (1) attached to the underlying sheaf of sets.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]

/-- **The finite locally constant sheaf of sets underlying `ℱ_ρ`**, on the site of Stacks 021B, as
a functor of `ρ`. -/
def representationSetSheaf :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
    (finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse ⋙
    (finiteLocallyConstantModuleSheafScalarActionEquivalence (SmallEtale.topology B X.1 X.2)
      Λ).functor ⋙ AdditiveFunctor.forget _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (SingleObj.star Λ) ⋙
    forgetFiniteLocallyConstantAbelianSheaf (SmallEtale.topology B X.1 X.2)

/-- **The finite étale cover representing `ℱ_ρ`**, as a finite object of the small étale site of
Stacks 021B and as a functor of `ρ`: the dictionary of Tag 03RV applied to the underlying sheaf of
sets. -/
def representationCoverSmall :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      (finiteSmallEtaleObjects B X).FullSubcategory :=
  representationSetSheaf B X x Λ ⋙
    (finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse

/-- The sheaf represented by the representing cover is the sheaf of sets underlying `ℱ_ρ`, by
the counit of the dictionary of Tag 03RV. -/
def representationCoverSmallIso :
    representationCoverSmall B X x Λ ⋙ finiteSmallEtaleToFiniteLocallyConstant B X ≅
      representationSetSheaf B X x Λ :=
  Functor.isoWhiskerLeft (representationSetSheaf B X x Λ)
    (finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.counitIso

/-- **The tautological section of `ℱ_ρ` over its representing cover**, on the site of Stacks 021B:
the section of the underlying sheaf of sets corresponding, under the identification of that sheaf
with the sheaf represented by the cover, to the identity of the cover. -/
def representationTautologicalSectionSmall
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((representationSetSheaf B X x Λ).obj ρ).obj.obj.obj
      (op ((representationCoverSmall B X x Λ).obj ρ).1) :=
  ((representationCoverSmallIso B X x Λ).hom.app ρ).hom.hom.app _
    (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
      ((representationCoverSmall B X x Λ).obj ρ).1)

/-- **The tautological section represents the sheaf of sets underlying `ℱ_ρ`**, on the site of
Stacks 021B: the map from the sheaf represented by the cover that it corresponds to is the
counit of Tag 03RV, an isomorphism. -/
theorem isIso_sectionEquiv_symm_representationTautologicalSectionSmall
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    IsIso ((Sheaf.sectionEquiv (SmallEtale.topology B X.1 X.2)).symm
      (representationTautologicalSectionSmall B X x Λ ρ)) := by
  have h := Sheaf.sectionEquiv_symm_comp (SmallEtale.topology B X.1 X.2)
    ((representationCoverSmallIso B X x Λ).hom.app ρ).hom
    (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
      ((representationCoverSmall B X x Λ).obj ρ).1)
  rw [representationTautologicalSectionSmall, h]
  have h2 : (Sheaf.sectionEquiv (SmallEtale.topology B X.1 X.2)).symm
      (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
        ((representationCoverSmall B X x Λ).obj ρ).1) = 𝟙 _ :=
    Equiv.symm_apply_apply _ _
  have hid : IsIso ((Sheaf.sectionEquiv (SmallEtale.topology B X.1 X.2)).symm
      (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
        ((representationCoverSmall B X x Λ).obj ρ).1)) := by
    rw [h2]
    infer_instance
  have : IsIso ((representationCoverSmallIso B X x Λ).hom.app ρ) :=
    Iso.isIso_hom ((representationCoverSmallIso B X x Λ).app ρ)
  exact IsIso.comp_isIso' hid (Functor.map_isIso (ObjectProperty.ι _)
    ((representationCoverSmallIso B X x Λ).hom.app ρ))

/-- The sheaf `ℱ_ρ` before it is moved to Mathlib's small étale site: the sheaf of Tag 0DV5 (3)
on the site of Stacks 021B, with its coefficients lifted to the universe of `ℱ_ρ`. -/
abbrev representationSheafLift
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) :=
  (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{0, u + 1} Λ)).obj
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj ρ).obj

/-- The equivalence between the sheaves of `Λ`-modules on the two presentations of the small étale
site, with the limits instance used by `AlgebraicGeometry.representationSheaf`. -/
abbrev representationSheafEquiv :=
  @SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{max (u + 1) 0} Λ) _
    (Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, 0, max (u + 1) 0} Λ)

/-- **The representing cover of `ℱ_ρ`, as an étale `X`-scheme of Mathlib's small étale site.** -/
abbrev representationCover
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    X.1.Etale :=
  (SmallEtale.toEtaleSite B X.1 X.2).obj ((representationCoverSmall B X x Λ).obj ρ).1

/-- **The tautological section of `ℱ_ρ` over its representing cover**, on Mathlib's small étale
site. -/
def representationTautologicalSection
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((representationSheaf B X x Λ).obj ρ).obj.obj (op (representationCover B X x Λ ρ)) :=
  (((representationSheafEquiv B X Λ).unitIso.hom.app
      (representationSheafLift B X x Λ ρ)).hom.app
      (op ((representationCoverSmall B X x Λ).obj ρ).1))
    (ULift.up (representationTautologicalSectionSmall B X x Λ ρ))

/-- The sheaf of sets underlying the lifted sheaf `representationSheafLift` is the sheaf of sets
underlying `ℱ_ρ` on the site of Stacks 021B, the universe lift being `ULift`. -/
def representationSetSheafUliftIso
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((representationSetSheaf B X x Λ).obj ρ).obj ≅
      (sheafCompose (SmallEtale.topology B X.1 X.2) (forget (ModuleCat.{u + 1} Λ))).obj
        (representationSheafLift B X x Λ ρ) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Equiv.toIso Equiv.ulift.symm)
    (fun _ ↦ rfl))

/-- **The tautological section represents the sheaf of sets underlying `ℱ_ρ`** on Mathlib's small
étale site: the map from the sheaf represented by the representing cover that it corresponds to
is an isomorphism. This is read off from the site of Stacks 021B, where it is the counit of
Tag 03RV, through the equivalence of the sheaves on the two sites. -/
theorem isIso_sectionEquiv_symm_representationTautologicalSection
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    IsIso ((Sheaf.sectionEquiv X.1.smallEtaleTopology).symm
      (Stacks.EtaleCohomology.forgetSection Λ ((representationSheaf B X x Λ).obj ρ)
        (representationTautologicalSection B X x Λ ρ))) := by
  rw [Sheaf.isIso_sectionEquiv_symm_iff]
  intro K
  let P := (SmallEtale.sheafEquiv B X.1 X.2 (Type (u + 1))).inverse
  let U := ((representationCoverSmall B X x Λ).obj ρ).1
  let ι : ((representationSetSheaf B X x Λ).obj ρ).obj ⟶
      P.obj ((Stacks.EtaleCohomology.etaleModuleUnderlyingSets Λ X.1).obj
        ((representationSheaf B X x Λ).obj ρ)) :=
    (representationSetSheafUliftIso B X x Λ ρ).hom ≫
      (sheafCompose (SmallEtale.topology B X.1 X.2) (forget (ModuleCat.{u + 1} Λ))).map
        ((representationSheafEquiv B X Λ).unitIso.hom.app (representationSheafLift B X x Λ ρ))
  have : IsIso ι := by
    have : IsIso ((sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget (ModuleCat.{u + 1} Λ))).map ((representationSheafEquiv B X Λ).unitIso.hom.app
          (representationSheafLift B X x Λ ρ))) := Functor.map_isIso _ _
    exact IsIso.comp_isIso' (Iso.isIso_hom _) this
  have hst := (Sheaf.isIso_sectionEquiv_symm_iff (SmallEtale.topology B X.1 X.2)
    ((representationSetSheaf B X x Λ).obj ρ).obj
      (representationTautologicalSectionSmall B X x Λ ρ)).mp
    (isIso_sectionEquiv_symm_representationTautologicalSectionSmall B X x Λ ρ) (P.obj K)
  have hf : (fun φ : (Stacks.EtaleCohomology.etaleModuleUnderlyingSets Λ X.1).obj
      ((representationSheaf B X x Λ).obj ρ) ⟶ K => φ.hom.app (op (representationCover B X x Λ ρ))
        (Stacks.EtaleCohomology.forgetSection Λ ((representationSheaf B X x Λ).obj ρ)
          (representationTautologicalSection B X x Λ ρ))) =
      (fun χ : ((representationSetSheaf B X x Λ).obj ρ).obj ⟶ P.obj K =>
          χ.hom.app (op U) (representationTautologicalSectionSmall B X x Λ ρ)) ∘
        (fun ψ => ι ≫ ψ) ∘ P.map := by
    funext φ
    rfl
  rw [hf]
  refine hst.comp (Function.Bijective.comp ?_
    ((SmallEtale.sheafEquiv B X.1 X.2 (Type (u + 1))).fullyFaithfulInverse.map_bijective _ _))
  exact (isIso_iff_coyoneda_map_bijective ι).mp inferInstance _

/-- The representing cover of `ℱ_ρ`, as a finite étale cover of `X`. -/
abbrev representationFiniteEtaleCover
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    FiniteEtaleOver X.1 :=
  (representingCover B X).obj ((representationSetSheaf B X x Λ).obj ρ)

/-- **The geometric fibre of the representing cover of `ℱ_ρ` is `M`.** The fibre at `x` of the
finite étale cover representing the underlying sheaf of sets of `ℱ_ρ` is the underlying set of
the `π₁(X, x)`-module that Tag 0DV5 (3) attaches to `ℱ_ρ` (`geometricFibreSetEquiv`), and that
module is `ρ` by the counit of Tag 0DV5 (3). -/
def representationFibreEquiv
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    finiteEtaleFiber x (representationFiniteEtaleCover B X x Λ ρ) ≃
      ρ.obj.obj.obj.V :=
  (geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ)).symm.trans
    ((finiteTypeContinuousModuleι Λ (EtaleFundamentalGroup X.1 x) ⋙
      continuousModuleToModuleCat Λ (EtaleFundamentalGroup X.1 x)).mapIso
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app
          ρ)).toLinearEquiv.toEquiv

/-- `AlgebraicGeometry.representationFibreEquiv` of `w` is the counit applied to any `z` that
`geometricFibreSetEquiv` sends to `w`. -/
private theorem representationFibreEquiv_eq_counit
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (w : finiteEtaleFiber x (representationFiniteEtaleCover B X x Λ ρ))
    (z : ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj ρ)).obj.obj.obj.V)
    (hz : geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ) z = w) :
    representationFibreEquiv B X x Λ ρ w =
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app
        ρ).hom.hom.hom.hom.hom z := by
  rw [← hz]
  change ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app
    ρ).hom.hom.hom.hom.hom
      ((geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ)).symm
        (geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ) z)) = _
  exact congrArg _ (Equiv.symm_apply_apply
    (geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ)) z)

/-- `AlgebraicGeometry.representationFibreEquiv` intertwines the monodromy action on the fibre
with the action `ρ`. -/
theorem representationFibreEquiv_smul
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (γ : EtaleFundamentalGroup X.1 x)
    (v : finiteEtaleFiber x (representationFiniteEtaleCover B X x Λ ρ)) :
    representationFibreEquiv B X x Λ ρ
        ((γ.asIso.app (representationFiniteEtaleCover B X x Λ ρ)).hom v) =
      finiteTypeContinuousModuleRepresentation Λ _ ρ γ (representationFibreEquiv B X x Λ ρ v) := by
  obtain ⟨a, rfl⟩ :=
    (geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ)).surjective v
  rw [representationFibreEquiv_eq_counit B X x Λ ρ _ _
      (geometricFibreSetEquiv_smul B X x ((representationSetSheaf B X x Λ).obj ρ) γ a),
    representationFibreEquiv_eq_counit B X x Λ ρ _ a rfl]
  exact finiteTypeContinuousModule_hom_comm
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app ρ).hom γ _

/-- `AlgebraicGeometry.representationFibreEquiv` is natural in `ρ`. -/
theorem representationFibreEquiv_naturality
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (φ : ρ ⟶ ρ') (v : finiteEtaleFiber x (representationFiniteEtaleCover B X x Λ ρ)) :
    representationFibreEquiv B X x Λ ρ' ((finiteEtaleFiberFunctor x).map
        ((representingCover B X).map ((representationSetSheaf B X x Λ).map φ)) v) =
      φ.hom.hom.hom.hom.hom (representationFibreEquiv B X x Λ ρ v) := by
  obtain ⟨a, rfl⟩ :=
    (geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ)).surjective v
  rw [representationFibreEquiv_eq_counit B X x Λ ρ' _
      (((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.map
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.map
          φ)).hom.hom.hom.hom.hom a)
      (geometricFibreSetEquiv_naturality B X x ((representationSetSheaf B X x Λ).map φ) a),
    representationFibreEquiv_eq_counit B X x Λ ρ _ a rfl]
  refine congrArg (fun f => f.hom.hom.hom.hom.hom a)
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.hom.naturality φ)

/-- Multiplication by a scalar on the sheaf of sets underlying `ℱ_ρ`, as an endomorphism of finite
locally constant sheaves of sets. -/
abbrev representationSetSheafScalar
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) (a : Λ) :
    (representationSetSheaf B X x Λ).obj ρ ⟶ (representationSetSheaf B X x Λ).obj ρ :=
  (forgetFiniteLocallyConstantAbelianSheaf (SmallEtale.topology B X.1 X.2)).map
    (((finiteLocallyConstantModuleSheafScalarActionEquivalence (SmallEtale.topology B X.1 X.2)
      Λ).functor.obj ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.obj
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj ρ))).obj.map
          (show SingleObj.star Λ ⟶ SingleObj.star Λ from a))

/-- `AlgebraicGeometry.representationFibreEquiv` carries the cover endomorphism representing
multiplication by `a` to multiplication by `a`. -/
theorem representationFibreEquiv_scalar
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) (a : Λ)
    (v : finiteEtaleFiber x (representationFiniteEtaleCover B X x Λ ρ)) :
    representationFibreEquiv B X x Λ ρ ((finiteEtaleFiberFunctor x).map
        ((representingCover B X).map (representationSetSheafScalar B X x Λ ρ a)) v) =
      a • representationFibreEquiv B X x Λ ρ v := by
  obtain ⟨m, rfl⟩ : ∃ m : ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj ρ)).obj.obj.obj.V,
      geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ) m = v :=
    (geometricFibreSetEquiv B X x ((representationSetSheaf B X x Λ).obj ρ)).surjective v
  rw [representationFibreEquiv_eq_counit B X x Λ ρ _
      (a • m)
      (geometricFibreSetEquiv_naturality B X x (representationSetSheafScalar B X x Λ ρ a) m),
    representationFibreEquiv_eq_counit B X x Λ ρ _ m rfl]
  exact LinearMap.map_smul (ModuleCat.Hom.hom
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app
      ρ).hom.hom.hom.hom.hom) a
    m

/-- **The tautological sections are natural.** For a morphism `f : A ⟶ A'` of finite locally
constant sheaves of sets on the site of Stacks 021B, `f` carries the tautological section of `A`
over its representing cover to the restriction of the tautological section of `A'` along the
morphism of representing covers induced by `f`. -/
theorem counitIso_tautologicalSection_naturality
    {A A' : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory} (f : A ⟶ A') :
    f.hom.hom.app (op ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1)
        (((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.counitIso.hom.app
            A).hom.hom.app _
          (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
            ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1)) =
      A'.obj.obj.map
        ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.map f).hom.op
        (((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.counitIso.hom.app
            A').hom.hom.app _
          (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
            ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A').1)) := by
  have hnat := congrArg (fun φ :
      ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse ⋙
      (finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.functor).obj A ⟶ A' =>
    φ.hom.hom.app (op ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1)
      (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
        ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1))
    ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.counitIso.hom.naturality f)
  refine hnat.symm.trans ?_
  have hy : ((finiteSmallEtaleToFiniteLocallyConstant B X).map
      ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.map f)).hom.hom.app
      (op ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1)
      (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
        ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1) =
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2)).obj
        ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A').1).obj.map
        ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.map f).hom.op
        (Sheaf.tautologicalSection (SmallEtale.topology B X.1 X.2)
          ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A').1) := by
    rw [Sheaf.map_op_tautologicalSection]
    have h1 := Sheaf.sectionEquiv_comp (SmallEtale.topology B X.1 X.2)
      (𝟙 ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2)).obj
        ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1))
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2)).map
        ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.map f).hom)
    rw [Category.id_comp] at h1
    exact h1.symm
  refine (congrArg (fun y =>
    ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.counitIso.hom.app A').hom.hom.app
      (op ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.obj A).1)
      y) hy).trans ?_
  exact ConcreteCategory.congr_hom
    (((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.counitIso.hom.app
      A').hom.hom.naturality
      ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.map f).hom.op) _

/-- The unit of the equivalence of sheaves sends a section of the lifted sheaf of the form
`ℱ(h) ε'` to the corresponding restriction of the tautological section on Mathlib's site. -/
private theorem representationSheafEquiv_unit_app_eq
    (ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (h : ((representationCoverSmall B X x Λ).obj ρ).1 ⟶
      ((representationCoverSmall B X x Λ).obj ρ').1)
    (s : (representationSheafLift B X x Λ ρ').obj.obj
      (op ((representationCoverSmall B X x Λ).obj ρ).1))
    (hs : s = (representationSheafLift B X x Λ ρ').obj.map h.op
      (ULift.up (representationTautologicalSectionSmall B X x Λ ρ'))) :
    ((representationSheafEquiv B X Λ).unitIso.hom.app
      (representationSheafLift B X x Λ ρ')).hom.app
        (op ((representationCoverSmall B X x Λ).obj ρ).1) s =
      ((representationSheaf B X x Λ).obj ρ').obj.map ((SmallEtale.toEtaleSite B X.1 X.2).map h).op
        (representationTautologicalSection B X x Λ ρ') := by
  subst hs
  exact ConcreteCategory.congr_hom (((representationSheafEquiv B X Λ).unitIso.hom.app
    (representationSheafLift B X x Λ ρ')).hom.naturality h.op) _

/-- Moving the tautological section to Mathlib's site: if a morphism `g` of lifted sheaves carries
the lifted tautological section of `ρ` to the restriction of that of `ρ'` along `h`, then the
corresponding morphism of sheaves on Mathlib's site carries the tautological section of `ρ` to the
restriction of that of `ρ'` along the image of `h`. -/
theorem representationTautologicalSection_transport
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (g : representationSheafLift B X x Λ ρ ⟶ representationSheafLift B X x Λ ρ')
    (h : ((representationCoverSmall B X x Λ).obj ρ).1 ⟶
      ((representationCoverSmall B X x Λ).obj ρ').1)
    (hg : g.hom.app (op ((representationCoverSmall B X x Λ).obj ρ).1)
        (ULift.up (representationTautologicalSectionSmall B X x Λ ρ)) =
      (representationSheafLift B X x Λ ρ').obj.map h.op
        (ULift.up (representationTautologicalSectionSmall B X x Λ ρ'))) :
    ((representationSheafEquiv B X Λ).functor.map g).hom.app (op (representationCover B X x Λ ρ))
        (representationTautologicalSection B X x Λ ρ) =
      ((representationSheaf B X x Λ).obj ρ').obj.map ((SmallEtale.toEtaleSite B X.1 X.2).map h).op
        (representationTautologicalSection B X x Λ ρ') := by
  have hn := congrArg (fun ψ => ψ.hom.app (op ((representationCoverSmall B X x Λ).obj ρ).1)
      (ULift.up (representationTautologicalSectionSmall B X x Λ ρ)))
    ((representationSheafEquiv B X Λ).unitIso.hom.naturality g)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hn
  exact hn.symm.trans (representationSheafEquiv_unit_app_eq B X x Λ ρ ρ' h _ hg)

/-- **The tautological sections are natural in `ρ`**: `ℱ_φ` carries the tautological section of
`ℱ_ρ` to the restriction of that of `ℱ_{ρ'}` along the morphism of representing covers. -/
theorem representationTautologicalSection_naturality
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (φ : ρ ⟶ ρ') :
    ((representationSheaf B X x Λ).map φ).hom.app (op (representationCover B X x Λ ρ))
        (representationTautologicalSection B X x Λ ρ) =
      ((representationSheaf B X x Λ).obj ρ').obj.map
        ((SmallEtale.toEtaleSite B X.1 X.2).map ((representationCoverSmall B X x Λ).map φ).hom).op
        (representationTautologicalSection B X x Λ ρ') :=
  representationTautologicalSection_transport B X x Λ _ _
    (congrArg ULift.up (counitIso_tautologicalSection_naturality B X
      ((representationSetSheaf B X x Λ).map φ)))

/-- **Scalars on the tautological section**: `a` times the tautological section of `ℱ_ρ` is its
restriction along the endomorphism of the representing cover that represents multiplication by
`a`. -/
theorem representationTautologicalSection_smul
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) (a : Λ) :
    a • representationTautologicalSection B X x Λ ρ =
      ((representationSheaf B X x Λ).obj ρ).obj.map
        ((SmallEtale.toEtaleSite B X.1 X.2).map
          ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.map
            (representationSetSheafScalar B X x Λ ρ a)).hom).op
        (representationTautologicalSection B X x Λ ρ) := by
  have hs := counitIso_tautologicalSection_naturality B X (representationSetSheafScalar B X x Λ ρ a)
  exact (LinearMap.map_smul (ModuleCat.Hom.hom (((representationSheafEquiv B X Λ).unitIso.hom.app
    (representationSheafLift B X x Λ ρ)).hom.app (op ((representationCoverSmall B X x Λ).obj ρ).1)))
      a (ULift.up (representationTautologicalSectionSmall B X x Λ ρ))).symm.trans
    (representationSheafEquiv_unit_app_eq B X x Λ ρ ρ _ _ (congrArg ULift.up hs))

end AlgebraicGeometry

end
