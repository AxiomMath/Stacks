module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SpecializationFiniteTypeLocallyConstantModuleConverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SmallEtaleSpecializationBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SmoothProperSpecializationHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallyConstant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of a smooth proper morphism over a Noetherian base

Let `f : X ⟶ S` be smooth and proper with `S` Noetherian, `Λ` a Noetherian ring and `F` a finite
type, locally constant sheaf of `Λ`-modules on `X_étale` whose stalk at every geometric point `x̄`
is killed by an integer prime to the residue characteristic of `x̄`. This file proves that every
`Rᵠ f_* F` is a finite type, locally constant sheaf of `Λ`-modules: the last paragraph of the proof
of [Stacks, Tag 0GLI].

* `Rᵠ f_* F` is the `q`-th cohomology sheaf of `Rf_! F` for the identity compactification of the
  proper `f`, hence constructible by [Stacks, Tag 0GL0]; its stalks are therefore finitely
  generated.
* Its specialization maps are bijective by [Stacks, Tag 0GKD], read on the underlying abelian
  sheaf, whose higher direct images are the underlying abelian sheaves of those of `F`.
* [Stacks, Tag 0GKC] concludes, `S` being Noetherian.

## Main definitions

* `Stacks.EtaleCohomology.rightDerivedIsoHomologyDerivedLowerShriekOfProper`:
  `Rᵠ f_* F ≅ Hᵠ(Rf_! F)` for a proper `f` compactified by itself.

## Main results

* `AlgebraicGeometry.bijective_specializationMapOnStalks_of_forget`: bijectivity of a
  specialization map of a presheaf of modules is detected on the underlying presheaf of sets.

In the namespace `Stacks.EtaleCohomology`:

* `isLocallyConstant_etaleModuleForget_of_isFiniteTypeLocallyConstantModuleSheaf`: the abelian
  sheaf underlying a finite type, locally constant sheaf of `Λ`-modules is locally constant.
* `isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper_of_isNoetherian`:
  for `f` smooth and proper over a Noetherian base, every `Rᵠ f_* F` is a finite type, locally
  constant sheaf of `Λ`-modules.

## References

* [Stacks Project, Tag 0GLI](https://stacks.math.columbia.edu/tag/0GLI)
* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 0GKD](https://stacks.math.columbia.edu/tag/0GKD)
* [Stacks Project, Tag 0GKC](https://stacks.math.columbia.edu/tag/0GKC)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe u r

attribute [local instance] AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_moduleCatMax

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Λ : Type r} [CommRing Λ]

/-- **Specialization maps of a presheaf of modules and of its underlying presheaf of sets.** The
specialization map of a presheaf of `Λ`-modules on the small étale site is bijective as soon as
that of its underlying presheaf of sets is: the stalk of the underlying presheaf of sets is the
set underlying the stalk, compatibly with germs, and both specialization maps act on germs by
moving the étale neighbourhood. -/
public theorem bijective_specializationMapOnStalks_of_forget {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ)
    (h : Function.Bijective
      (specializationMapOnStalks σ (P ⋙ forget (ModuleCat.{max (u + 1) r} Λ)))) :
    Function.Bijective (specializationMapOnStalks σ P) := by
  let F := forget (ModuleCat.{max (u + 1) r} Λ)
  let es := ((geometricPointSitePoint B S hS s).presheafFiberCompIso F).app P
  let et := ((geometricPointSitePoint B S hS σ.target).presheafFiberCompIso F).app P
  have hcomm : ∀ a : etaleStalk B S hS s (P ⋙ F),
      specializationMapOnStalks σ P (es.hom a) =
        et.hom (specializationMapOnStalks σ (P ⋙ F) a) := by
    intro a
    obtain ⟨U, x, c, rfl⟩ :=
      (geometricPointSitePoint B S hS s).toPresheafFiber_jointly_surjective (P := P ⋙ F) a
    have h1 := ConcreteCategory.congr_hom
      ((geometricPointSitePoint B S hS s).toPresheafFiber_presheafFiberCompIso_hom_app F U x P) c
    have h2 := ConcreteCategory.congr_hom
      ((geometricPointSitePoint B S hS σ.target).toPresheafFiber_presheafFiberCompIso_hom_app
        F U ((specializationFiberHom σ).app U x) P) c
    have h3 : specializationMapOnStalks σ (P ⋙ F)
        ((geometricPointSitePoint B S hS s).toPresheafFiber U x (P ⋙ F) c) =
        (geometricPointSitePoint B S hS σ.target).toPresheafFiber U
          ((specializationFiberHom σ).app U x) (P ⋙ F) c :=
      ConcreteCategory.congr_hom (ι_comp_specializationMapOnStalks σ (P ⋙ F)
        (Functor.elementsMk (geometricPointFiber B S hS s) U x)) c
    simp only [ConcreteCategory.comp_apply] at h1 h2
    change specializationMapOnStalks σ P (es.hom _) = et.hom _
    rw [h3]
    change specializationMapOnStalks σ P
        (((geometricPointSitePoint B S hS s).presheafFiberCompIso F).hom.app P _) =
      ((geometricPointSitePoint B S hS σ.target).presheafFiberCompIso F).hom.app P _
    rw [h1, h2]
    exact ConcreteCategory.congr_hom
      (toPresheafFiber_comp_specializationMapOnStalks B S hS Λ (P := P) σ x) c
  have hes : Function.Bijective es.hom := es.toEquiv.bijective
  have het : Function.Bijective et.hom := et.toEquiv.bijective
  have hfun : (fun y => specializationMapOnStalks σ P y) ∘ (fun a => es.hom a) =
      (fun b => et.hom b) ∘ (fun a => specializationMapOnStalks σ (P ⋙ F) a) :=
    funext hcomm
  have hR : Function.Bijective
      ((fun b => et.hom b) ∘ (fun a => specializationMapOnStalks σ (P ⋙ F) a)) := het.comp h
  rw [← hfun] at hR
  exact (Function.Bijective.of_comp_iff _ hes).1 hR

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

section LowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (Λ : Type) [CommRing Λ]

/-- **`Rⁿ f_* F` is the `n`-th cohomology sheaf of `Rf_! F`** for a proper `f` compactified by
itself. -/
def rightDerivedIsoHomologyDerivedLowerShriekOfProper (F : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived n).obj F ≅
      (DerivedCategory.Plus.homologyFunctor _ n).obj
        ((derivedLowerShriek.{u, 0} f (CompactificationOf.ofProper f) Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} Λ f) n).app F ≪≫
    (DerivedCategory.Plus.homologyFunctor _ n).mapIso
      ((derivedLowerShriekOfProperIso Λ f).app _).symm

end LowerShriek

/-! ### The abelian sheaf underlying a finite type locally constant sheaf -/

/-- **The abelian sheaf underlying a finite type locally constant sheaf of `Λ`-modules is locally
constant**: forgetting the module structure carries the constant sheaf of `Λ`-modules on `E` to
the constant abelian sheaf on the group underlying `E`. -/
theorem isLocallyConstant_etaleModuleForget_of_isFiniteTypeLocallyConstantModuleSheaf
    {X : Scheme.{u}} (Λ : Type) [CommRing Λ] (F : EtaleModules.{u, 0} Λ X)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.smallEtaleTopology Λ F) :
    Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology
      ((etaleModuleForget Λ X).obj F) := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, g, hcov, h⟩ := hF U
  refine ⟨I, V, g, hcov, fun i => ?_⟩
  obtain ⟨E, -, ⟨e⟩⟩ := h i
  let J' := X.smallEtaleTopology.over (V i)
  have := ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ J'
  have := ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ J'
  exact ⟨(forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj E,
    ⟨((constantCommuteCompose J'
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app E).symm ≪≫
      (sheafCompose J' (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso e⟩⟩

/-! ### The Noetherian case -/

section Noetherian

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (Λ : Type) [CommRing Λ]
  [IsNoetherianRing Λ]

/-- Let `f : X ⟶ S` be smooth and proper with `S` Noetherian, `Λ` a Noetherian ring and `F` a
finite type, locally constant sheaf of `Λ`-modules on `X_étale` such that the stalk at every
geometric point `x̄` is annihilated by an integer `n > 0` prime to the residue characteristic of
`x̄`. Then `Rᵠ f_* F` is a finite type, locally constant sheaf of `Λ`-modules for every `q`. -/
@[sga "1 XIII 1.16" "special case",
  sga "1 XIII 2.7" "Clause 2), special case",
  sga "1 XIII 2.9" "special case",
  sga "4 XVI 2.1" "special case",
  sga "4 XVI 2.2" "special case",
  sga "4½ Arcata 5.3.1" "special case"]
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper_of_isNoetherian
    [IsNoetherian S] (F : EtaleModules.{u, 0} Λ X)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.smallEtaleTopology Λ F)
    (htors : ∀ x : GeometricPoint X, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ X).obj F), n • a = 0)
    (q : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} S.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) := by
  let B := BigEtaleSite.containing S
  have hS : B.Contains S := BigEtaleSite.contains_containing S
  have hX : B.Contains X := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hS
  let SB : B.Scheme := B.obj S hS
  let XB : B.Scheme := B.obj X hX
  let G := ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F
  -- `F` is constructible and torsion
  have hFc : IsBigSiteConstructibleEtaleModule B XB Λ F :=
    isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B XB Λ _
      ((SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B XB Λ F).2 hF)
  have hFt : IsTorsionEtaleModule Λ X F :=
    torsionSheafProperty_of_forall_smallEtaleStalkAb _ fun t g =>
      let ⟨n, hn, _, h⟩ := htors t
      ⟨n, hn, h g⟩
  -- `G = Rᵠ f_* F` is constructible (Stacks 0GL0)
  have hGc : IsBigSiteConstructibleEtaleModule B SB Λ G :=
    IsBigSiteConstructibleEtaleModule.of_iso B Λ
      (rightDerivedIsoHomologyDerivedLowerShriekOfProper f Λ F q).symm
      (lowerShriekConstructibilityInput B (X := XB) (Y := SB) f (CompactificationOf.ofProper f)
        Λ F hFc hFt q)
  let G' := (etaleModulesToSmallEtale B SB Λ).obj G
  have hfin : ∀ s : GeometricPoint S, ModuleCat.isFG Λ (etaleStalk B S hS s G'.obj) :=
    fun s => isFG_etaleStalk_of_isConstructibleModuleSheaf B Λ SB G' hGc s
  -- the specialization maps of `G` are bijective (Stacks 0GKD)
  have hlc := isLocallyConstant_etaleModuleForget_of_isFiniteTypeLocallyConstantModuleSheaf Λ F hF
  have hsp : ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
      Function.Bijective (specializationMapOnStalks σ G'.obj) := by
    intro s σ
    apply bijective_specializationMapOnStalks_of_forget
    rw [geometricSpecialization_eq_ofPoint B S hS σ]
    have h0 := isIso_smallEtaleSpecializationStalkAb_app_rightDerived_of_smooth_of_isProper B S hS
      s σ.point hX f ((etaleModuleForget Λ X).obj F) hlc
      (fun x a => let ⟨n, hn, hc, h⟩ := htors x; ⟨n, hn, hc, h a⟩) q
    have h1 : IsIso ((smallEtaleSpecializationStalkAb B S hS s σ.point).app
        ((etaleModuleForget Λ S).obj G)) :=
      (NatTrans.isIso_app_iff_of_iso _
        ((rightDerivedEtaleModuleDirectImageForgetIso Λ f q).app F)).2 h0
    exact bijective_specializationMapOnStalks_transport B S hS ((etaleModuleForget Λ S).obj G)
      s σ.point h1
  have hScomp : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite :=
    fun V _ => TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hG' := isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk B S hS Λ hScomp G'
    hfin hsp
  exact (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B SB Λ G).1 hG'

end Noetherian

end Stacks.EtaleCohomology

end
